#[test]
fn subproof() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
        ",
        "Simple working examples" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (step t1.t2 (cl q) :rule hole)
            (step t1 (cl (not p) q) :rule subproof :discharge (t1.h1))": true,

            "(anchor :step t1)
            (assume t1.h1 p)
            (assume t1.h2 q)
            (step t1.t3 (cl) :rule hole)
            (step t1.t4 (cl (= r s)) :rule hole)
            (step t1 (cl (not p) (not q) (= r s))
                :rule subproof :discharge (t1.h1 t1.h2))": true,
        }
        "Missing assumption" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (step t1.t2 (cl (= r s)) :rule hole)
            (step t1 (cl (not p) (not q) (= r s)) :rule subproof :discharge (t1.h1))": false,
        }
        "Assumption terms don't match" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (assume t1.h2 q)
            (step t1.t3 (cl (= r s)) :rule hole)
            (step t1 (cl (not q) (not p) (= r s))
                :rule subproof :discharge (t1.h1 t1.h2))": false,

            "(anchor :step t1)
            (assume t1.h1 (or p q))
            (assume t1.h2 (= p q))
            (step t1.t3 (cl (= r s)) :rule hole)
            (step t1 (cl (not (and p q)) (not (= q p)) (= r s))
                :rule subproof :discharge (t1.h1 t1.h2))": false,
        }
        "Conclusion terms don't match" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (assume t1.h2 q)
            (step t1.t3 (cl (= r s)) :rule hole)
            (step t1 (cl (not p) (not q) (not (= r s)))
                :rule subproof :discharge (t1.h1 t1.h2))": false,
        }
        "Empty clause" {
            "(anchor :step t1)
            (assume t1.h1 p)
            (step t1.t2 (cl) :rule hole)
            (step t1 (cl (not p) false) :rule subproof :discharge (t1.h1))": true,
        }
    }
}

#[test]
fn bind() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": true,

            "(anchor :step t1 :args ((y1 Real) (y2 Real) (:= (x1 Real) y1) (:= (x2 Real) y2)))
            (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
            (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": true,
        }
        "Examples with binding arguments" {
            "(anchor :step t1 :args ((y Real) (z Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (forall ((x Real) (z Real)) p)
                (forall ((y Real) (z Real)) q))) :rule bind)": true,
        }
        "Out-of-place variable argument in anchor" {
            "(anchor :step t1 :args ((y1 Real) (:= (x1 Real) y1) (y2 Real) (:= (x2 Real) y2)))
            (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
            (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": false,
        }
        "Binding `lambda` and `choice` terms" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= x y)) :rule hole)
            (step t1 (cl (= (lambda ((x Real)) x) (lambda ((y Real)) y))) :rule bind)": true,

            "(anchor :step t1 :args ((y Int) (:= (x Int) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (choice ((x Int)) p) (choice ((y Int)) q))) :rule bind)": true,
        }
        "y_i appears in phi as a free variable" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= (= y x) (= y y))) :rule hole)
            (step t1 (cl (= (forall ((x Real)) (= y x))
                (forall ((y Real)) (= y y)))) :rule bind)": false,

            "(anchor :step t1 :args ((y Real) (z Real) (:= (x Real) y)))
            (step t1.t1 (cl (= (= y x) (= y y))) :rule hole)
            (step t1 (cl (= (forall ((z Real) (x Real)) (= y z))
                (forall ((z Real) (y Real)) (= y z)))) :rule bind)": false,
        }
        "Terms in conclusion clause don't match terms in previous command" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1.t2 (cl (= r s)) :rule hole) ; This step shouldn't be here!
            (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": false,

            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (forall ((x Real)) q) (forall ((y Real)) p))) :rule bind)": false,
        }
        "Context substitutions don't match quantifier bindings" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= p q)) :rule hole)
            (step t1 (cl (= (forall ((y Real)) p) (forall ((x Real)) q))) :rule bind)": false,

            "(anchor :step t1 :args ((y1 Real) (y2 Real) (:= (x1 Real) y1) (:= (x2 Real) y2)))
            (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
            (step t1 (cl (= (forall ((x2 Real)) (= x1 x2))
                (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": false,
        }
    }
}

#[test]
fn r#let() {
    test_cases! {
        definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun i () Int)
            (declare-fun j () Int)
            (declare-fun k () Int)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (declare-fun z () Int)
        ",
        "Simple working examples" {
            "(step t1 (cl (= i x)) :rule hole)
            (anchor :step t2 :args ((x Int) (:= (a Int) x)))
            (step t2.t1 (cl (= p q)) :rule hole)
            (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,

            "(step t1 (cl (= i x)) :rule hole)
            (step t2 (cl (= k z)) :rule hole)
            (anchor :step t3 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
            (step t3.t1 (cl (= p q)) :rule hole)
            (step t3 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": true,
        }
        "Premise equalities may be flipped" {
            "(step t1 (cl (= x i)) :rule hole)
            (anchor :step t2 :args ((x Int) (:= (a Int) x)))
            (step t2.t1 (cl (= p q)) :rule hole)
            (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,
        }
        "Wrong number of premises" {
            "(step t1 (cl (= i x)) :rule hole)
            (anchor :step t2 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
            (step t2.t1 (cl (= p q)) :rule hole)
            (step t2 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1))": false,

            "(step t1 (cl (= i x)) :rule hole)
            (step t2 (cl (= y y)) :rule hole)
            (step t3 (cl (= k z)) :rule hole)
            (anchor :step t4 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
            (step t4.t1 (cl (= p q)) :rule hole)
            (step t4 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": false,
        }
        "Number of bindings is `let` term doesn't match number of substitutions in context" {
            "(step t1 (cl (= i x)) :rule hole)
            (step t2 (cl (= j y)) :rule hole)
            (anchor :step t3 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
            (step t3.t1 (cl (= p q)) :rule hole)
            (step t3 (cl (= (let ((a i) (b j)) p) q)) :rule let :premises (t1 t2))": false,
        }
        "u and u' don't match equality in previous command" {
            "(step t1 (cl (= i x)) :rule hole)
            (anchor :step t2 :args ((x Int) (:= (a Int) x)))
            (step t2.t1 (cl (= p (= i j))) :rule hole)
            (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": false,
        }
    }
}

#[test]
fn onepoint() {
    test_cases! {
        definitions = "
            (declare-const p Bool)
            (declare-const t Int)
            (declare-const u Int)
            (declare-const v Int)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (=> (= x t) p) (=> (= t t) p))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (=> (= x t) p)) (=> (= t t) p)))
                :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (or (not (= x t)) p) (or (not (= t t)) p))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (or (not (= x t)) p)) (or (not (= t t)) p)))
                :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (and (= x t) p) (and (= t t) p))) :rule hole)
            (step t1 (cl (= (exists ((x Int)) (and (= x t) p)) (and (= t t) p)))
                :rule onepoint)": true,
        }
        "Multiple quantifier bindings" {
            "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
            (step t1.t1 (cl (= (=> (= z t) (= (+ x y) (+ z t)))
                               (=> (= t t) (= (+ x y) (+ t t))))) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int) (z Int)) (=> (= z t) (= (+ x y) (+ z t))))
                (forall ((x Int) (y Int))         (=> (= t t) (= (+ x y) (+ t t))))
            )) :rule onepoint)": true,

            "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
            (step t1.t1 (cl (= (and (= z t) (= (+ x y) (+ z t)))
                               (and (= t t) (= (+ x y) (+ t t))))) :rule hole)
            (step t1 (cl (=
                (exists ((x Int) (y Int) (z Int)) (and (= z t) (= (+ x y) (+ z t))))
                (exists ((x Int) (y Int))         (and (= t t) (= (+ x y) (+ t t))))
            )) :rule onepoint)": true,
        }
        "Multiple quantifier bindings eliminated" {
            "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
            (step t1.t1 (cl (= (=> (= x t) (=> (= y u) (=> (= z v) p)))
                               (=> (= t t) (=> (= u u) (=> (= v v) p))))) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int) (z Int)) (=> (= x t) (=> (= y u) (=> (= z v) p))))
                (=> (= t t) (=> (= u u) (=> (= v v) p)))
            )) :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
            (step t1.t1 (cl (= (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p)))
                               (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
            )) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int) (z Int))
                    (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p))))
                (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
            )) :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
            (step t1.t1 (cl (= (=> (and (= x t) (and (= y u) (= z v))) p)
                               (=> (and (= t t) (and (= u u) (= v v))) p))) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int) (z Int)) (=> (and (= x t) (and (= y u) (= z v))) p))
                (=> (and (= t t) (and (= u u) (= v v))) p)
            )) :rule onepoint)": true,

            "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
            (step t1.t1 (cl (= (and (= x t) (and (= y u) (and (= z v) p)))
                               (and (= t t) (and (= u u) (and (= v v) p))))) :rule hole)
            (step t1 (cl (=
                (exists ((x Int) (y Int) (z Int)) (and (= x t) (and (= y u) (and (= z v) p))))
                (and (= t t) (and (= u u) (and (= v v) p)))
            )) :rule onepoint)": true,
        }
        "Multiple occurrences with different polarity" {
            // This test reproduces a bug that existed where the cache didn't take into account
            // the polarity of a seen term.
            "(anchor :step t3 :args ((:= (?x Int) 0)))
            (step t3.t8 (cl (=
                (=> (not (= 0 ?x)) (=> (= 2 2) (=> (= 0 ?x) (= 1 2))))
                (=> (not (= 0 0)) (=> (= 2 2) (=> (= 0 0) (= 1 2))))
            )) :rule hole)
            (step t3 (cl (=
                (forall ((?x Int)) (=> (not (= 0 ?x)) (=> (= 2 2) (=> (= 0 ?x) (= 1 2)))))
                (=> (not (= 0 0)) (=> (= 2 2) (=> (= 0 0) (= 1 2))))
            )) :rule onepoint)": true,
        }
        // Added in Clean: `extract_points` descended through nested binders keeping the points it
        // found there, so a point under a binder that rebinds the eliminated variable, or whose
        // term mentions a variable that binder binds, was read as a point for the outer variable
        // (see third-party/carcara/DOWNSTREAM.md)
        "The point may not come from under a binder that rebinds it" {
            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (=> (exists ((x Int)) (= x t)) (= x t))
                               (=> (exists ((x Int)) (= x t)) (= t t)))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (=> (exists ((x Int)) (= x t)) (= x t)))
                            (=> (exists ((x Int)) (= x t)) (= t t))))
                :rule onepoint)": false,

            // The only `(= x t)` here is the shadowed one; `(< x u)` is not a point
            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (and (exists ((x Int)) (= x t)) (< x u))
                               (and (exists ((x Int)) (= x t)) (< t u)))) :rule hole)
            (step t1 (cl (= (exists ((x Int)) (and (exists ((x Int)) (= x t)) (< x u)))
                            (and (exists ((x Int)) (= x t)) (< t u))))
                :rule onepoint)": false,

            // The point's term is the `u` bound by the inner `exists`, not the free `u`
            "(anchor :step t1 :args ((:= (x Int) u)))
            (step t1.t1 (cl (= (=> (exists ((u Int)) (= x u)) (= x t))
                               (=> (exists ((u_renamed Int)) (= u u_renamed)) (= u t)))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (=> (exists ((u Int)) (= x u)) (= x t)))
                            (=> (exists ((u_renamed Int)) (= u u_renamed)) (= u t))))
                :rule onepoint)": false,

            // A nested binder that shadows neither the point nor its term is still fine
            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (=> (and (= x t) (exists ((w Int)) (= w u))) p)
                               (=> (and (= t t) (exists ((w Int)) (= w u))) p))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (=> (and (= x t) (exists ((w Int)) (= w u))) p))
                            (=> (and (= t t) (exists ((w Int)) (= w u))) p)))
                :rule onepoint)": true,

            // The point may sit under a binder that binds something else
            "(anchor :step t1 :args ((:= (x Int) t)))
            (step t1.t1 (cl (= (=> (exists ((w Int)) (= x t)) p)
                               (=> (exists ((w Int)) (= t t)) p))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (=> (exists ((w Int)) (= x t)) p))
                            (=> (exists ((w Int)) (= t t)) p)))
                :rule onepoint)": true,
        }
    }
}

#[test]
fn sko_ex() {
    test_cases! {
        definitions = "
            (declare-fun p (Int) Bool)
            (declare-fun q (Int) Bool)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((:= (x Int) (choice ((x Int)) (p x)))))
            (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (p x))))) :rule hole)
            (step t1 (cl (= (exists ((x Int)) (p x)) (p (choice ((x Int)) (p x)))))
                :rule sko_ex)": true,

            "(anchor :step t1 :args (
                (:= (x Int) (choice ((x Int)) (exists ((y Int)) (= x y))))
                (:= (y Int) (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
            ))
            (step t1.t1 (cl (=
                (= x y)
                (= (choice ((x Int)) (exists ((y Int)) (= x y)))
                   (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
            )) :rule hole)
            (step t1 (cl (=
                (exists ((x Int) (y Int)) (= x y))
                (= (choice ((x Int)) (exists ((y Int)) (= x y)))
                   (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
            )) :rule sko_ex)": true,
        }
    }
}

#[test]
fn sko_forall() {
    test_cases! {
        definitions = "
            (declare-fun p (Int) Bool)
            (declare-fun q (Int) Bool)
        ",
        "Simple working examples" {
            "(anchor :step t1 :args ((:= (x Int) (choice ((x Int)) (not (p x))))))
            (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (not (p x)))))) :rule hole)
            (step t1 (cl (= (forall ((x Int)) (p x)) (p (choice ((x Int)) (not (p x))))))
                :rule sko_forall)": true,

            "(anchor :step t1 :args (
                (:= (x Int) (choice ((x Int)) (not (forall ((y Int)) (= x y)))))
                (:= (y Int)
                    (choice ((y Int))
                        (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
            ))
            (step t1.t1 (cl (=
                (= x y)
                (= (choice ((x Int)) (not (forall ((y Int)) (= x y))))
                    (choice ((y Int))
                        (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
            )) :rule hole)
            (step t1 (cl (=
                (forall ((x Int) (y Int)) (= x y))
                (= (choice ((x Int)) (not (forall ((y Int)) (= x y))))
                    (choice ((y Int))
                        (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
            )) :rule sko_forall)": true,
        }
    }
}

// Added in Clean: `bind` must rename bound variables into context variables. Every `false` case
// below was accepted by upstream Carcara and is false in some model (see
// third-party/carcara/DOWNSTREAM.md).
#[test]
fn bind_renaming() {
    test_cases! {
        definitions = "
            (declare-sort U 0)
            (declare-fun P (U) Bool)
            (declare-fun f (U) U)
            (declare-fun y () Real)
        ",
        "Right-hand binder is not a context variable" {
            "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
            (step t1.t1 (cl (= (= y x) (= y y))) :rule refl)
            (step t1 (cl (= (forall ((x Real)) (= y x)) (forall ((s Real)) (= y y)))) :rule bind)": false,
        }
        "Renamed variable is not bound on the left" {
            "(anchor :step t1 :args ((y U) (:= (x U) y)))
            (step t1.t1 (cl (= (P x) (P y))) :rule refl)
            (step t1 (cl (= (forall ((y U)) (P x)) (forall ((y U)) (P y)))) :rule bind)": false,
        }
        "Renamed variable is not bound on the right" {
            "(anchor :step t1 :args ((y U) (:= (x U) y)))
            (step t1.t1 (cl (= x y)) :rule refl)
            (step t1.t2 (cl (= (f x) (f y))) :rule cong :premises (t1.t1))
            (step t1.t3 (cl (= (P (f x)) (P (f y)))) :rule cong :premises (t1.t2))
            (step t1 (cl (= (exists ((x U)) (P (f x))) (exists ((x U)) (P (f y))))) :rule bind)": false,
        }
        "Correct renaming" {
            "(anchor :step t1 :args ((y U) (:= (x U) y)))
            (step t1.t1 (cl (= x y)) :rule refl)
            (step t1.t2 (cl (= (f x) (f y))) :rule cong :premises (t1.t1))
            (step t1.t3 (cl (= (P (f x)) (P (f y)))) :rule cong :premises (t1.t2))
            (step t1 (cl (= (exists ((x U)) (P (f x))) (exists ((y U)) (P (f y))))) :rule bind)": true,
        }
    }
}

// Added in Clean: the step that ends an anchor with arguments is exported to the enclosing proof,
// so it must discharge the context. Both `false` cases were accepted by upstream Carcara and
// export `(= (P x) (P a))`, which is false when `x` is not `a` (see
// third-party/carcara/DOWNSTREAM.md).
#[test]
fn context_subproofs_end_with_a_context_rule() {
    test_cases! {
        definitions = "
            (declare-sort U 0)
            (declare-fun P (U) Bool)
            (declare-const a U)
            (declare-const p Bool)
        ",
        "Anchor with arguments ended by another rule" {
            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P x) (P a))) :rule refl)
            (step t1 (cl (= (P x) (P a))) :rule subproof)": false,

            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P x) (P a))) :rule refl)
            (step t1 (cl (= (P x) (P a))) :rule refl)": false,
        }
        "Anchors ended correctly" {
            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (=> (= x a) (P x)) (=> (= a a) (P a)))) :rule refl)
            (step t1 (cl (= (forall ((x U)) (=> (= x a) (P x))) (=> (= a a) (P a)))) :rule onepoint)": true,

            "(anchor :step t1)
            (assume t1.h1 p)
            (step t1.t2 (cl p) :rule reordering :premises (t1.h1))
            (step t1 (cl (not p) p) :rule subproof :discharge (t1.h1))": true,
        }
    }
}

// Added in Clean: a point `(= x t)` eliminates `x` only when `t` does not depend on `x` (or on a
// variable eliminated after it). Upstream Carcara accepted the first case, which is false when
// `P` holds at `a` but not everywhere (see third-party/carcara/DOWNSTREAM.md).
#[test]
fn onepoint_points_do_not_mention_the_eliminated_variable() {
    test_cases! {
        definitions = "
            (declare-sort U 0)
            (declare-fun P (U) Bool)
            (declare-fun Q (U U) Bool)
            (declare-fun f (U) U)
            (declare-const a U)
        ",
        "Point mentions the eliminated variable" {
            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (=> (= x x) (P x)) (=> (= a a) (P a)))) :rule refl)
            (step t1 (cl (= (forall ((x U)) (=> (= x x) (P x))) (=> (= a a) (P a)))) :rule onepoint)": false,
        }
        "Triangular points" {
            "(anchor :step t1 :args ((:= (x U) a) (:= (y U) (f a))))
            (step t1.t1 (cl (= (=> (= x a) (=> (= y (f x)) (Q x y))) (=> (= a a) (=> (= (f a) (f a)) (Q a (f a)))))) :rule refl)
            (step t1 (cl (= (forall ((x U) (y U)) (=> (= x a) (=> (= y (f x)) (Q x y))))
                            (=> (= a a) (=> (= (f a) (f a)) (Q a (f a)))))) :rule onepoint)": true,
        }
    }
}

// Added in Clean: the variables an anchor binds shadow the same names outside it. Every `false`
// case was accepted by upstream Carcara and exports a clause that is false in some model: a
// closing rule exported a term mentioning a constrained variable, a step inside the anchor used a
// premise in which the same name meant the outer variable, or an assigned value mentioned a name
// that the anchor (or a nested one) binds, so the context substitution moved it into another
// scope (see third-party/carcara/DOWNSTREAM.md).
#[test]
fn anchor_variables_are_scoped() {
    test_cases! {
        definitions = "
            (declare-sort U 0)
            (declare-fun P (U) Bool)
            (declare-fun Q (U U) Bool)
            (declare-fun f (U) U)
            (declare-const a U)
            (declare-const b U)
            (declare-const x U)
            (declare-const y U)
        ",
        "Closing rule exports a constrained variable" {
            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P x) (P x))) :rule refl)
            (step t1 (cl (= (let ((x a)) (P x)) (P x))) :rule let)": false,

            "(assume h (= a b))
            (anchor :step t1 :args ((:= (x U) b)))
            (step t1.t1 (cl (= (Q x a) (Q x a))) :rule refl)
            (step t1 (cl (= (let ((x a)) (Q x a)) (Q x a))) :rule let :premises (h))": false,

            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (=> (= x a) (P x)) (=> (= a a) (P x)))) :rule refl)
            (step t1 (cl (= (forall ((x U)) (=> (= x a) (P x))) (=> (= a a) (P x)))) :rule onepoint)": false,

            "(anchor :step t1 :args ((:= (x U) a) (:= (y U) (f a))))
            (step t1.t1 (cl (= (=> (= x a) (=> (= y (f x)) (Q x y))) (=> (= a a) (=> (= y (f a)) (Q a (f a)))))) :rule refl)
            (step t1 (cl (= (forall ((x U) (y U)) (=> (= x a) (=> (= y (f x)) (Q x y))))
                            (=> (= a a) (=> (= y (f a)) (Q a (f a)))))) :rule onepoint)": false,

            "(anchor :step t1 :args ((:= (x U) (choice ((x U)) (P x)))))
            (step t1.t1 (cl (= (P x) (P x))) :rule refl)
            (step t1 (cl (= (exists ((x U)) (P x)) (P x))) :rule sko_ex)": false,

            "(anchor :step t1 :args ((:= (x U) (choice ((x U)) (not (P x))))))
            (step t1.t1 (cl (= (P x) (P x))) :rule refl)
            (step t1 (cl (= (forall ((x U)) (P x)) (P x))) :rule sko_forall)": false,

            "(anchor :step t1 :args ((z U) (:= (x U) z)))
            (step t1.t1 (cl (= (P x) (P x))) :rule refl)
            (step t1 (cl (= (forall ((x U)) (P x)) (forall ((z U)) (P x)))) :rule bind)": false,
        }
        "Premise crosses an anchor that rebinds its variable" {
            "(assume h (= x b))
            (anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P x) (P b))) :rule cong :premises (h))
            (step t1 (cl (= (let ((x a)) (P x)) (P b))) :rule let)": false,

            "(assume h (= x b))
            (anchor :step t1 :args ((z U) (:= (x U) z)))
            (step t1.t1 (cl (= (P x) (P b))) :rule cong :premises (h))
            (step t1 (cl (= (forall ((x U)) (P x)) (forall ((z U)) (P b)))) :rule bind)": false,

            "(assume h (= y b))
            (anchor :step t1 :args ((y U) (:= (x U) y)))
            (step t1.t1 (cl (= (P x) (P y))) :rule refl)
            (step t1.t2 (cl (= (P y) (P b))) :rule cong :premises (h))
            (step t1.t3 (cl (= (P x) (P b))) :rule trans :premises (t1.t1 t1.t2))
            (step t1 (cl (= (forall ((x U)) (P x)) (forall ((y U)) (P b)))) :rule bind)": false,

            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= x a)) :rule refl)
            (step t1.t2 (cl (= (P x) (P a))) :rule refl)
            (step t1 (cl (= (let ((x x)) (P x)) (P a))) :rule let :premises (t1.t1))": false,
        }
        "Assigned value mentions a name bound by the anchor" {
            "(anchor :step t1 :args ((:= (x U) (f x))))
            (step t1.t1 (cl (= (P x) (P x))) :rule refl)
            (step t1 (cl (= (let ((x (f x))) (P x)) (P x))) :rule let)": false,

            "(anchor :step t1 :args ((x U) (y U) (:= (x U) y) (:= (y U) x)))
            (step t1.t1 (cl (= (Q x y) (Q y y))) :rule refl)
            (step t1 (cl (= (forall ((x U) (y U)) (Q x y)) (forall ((y U) (x U)) (Q y y)))) :rule bind)": false,

            "(anchor :step t1 :args ((:= (x U) (f y))))
            (anchor :step t1.t1 :args ((y U) (:= (w U) y)))
            (step t1.t1.t1 (cl (= (P x) (P (f y)))) :rule refl)
            (step t1.t1 (cl (= (forall ((w U)) (P x)) (forall ((y U)) (P (f y))))) :rule bind)
            (step t1 (cl (= (let ((x (f y))) (forall ((w U)) (P x))) (forall ((y U)) (P (f y))))) :rule let)": false,
        }
        "Bind renames onto a variable bound on the left" {
            "(anchor :step t1 :args ((z U) (y U) (:= (y U) z) (:= (x U) y)))
            (step t1.t1 (cl (= (Q x y) (Q z z))) :rule refl)
            (step t1 (cl (= (forall ((y U) (x U)) (Q x y)) (forall ((z U) (y U)) (Q z z)))) :rule bind)": false,
        }
        "Scoped anchors" {
            "(anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P x) (P a))) :rule refl)
            (step t1 (cl (= (let ((x a)) (P x)) (P a))) :rule let)": true,

            "(assume h (= a b))
            (anchor :step t1 :args ((:= (x U) a)))
            (step t1.t1 (cl (= (P a) (P b))) :rule cong :premises (h))
            (step t1.t2 (cl (= (P x) (P a))) :rule refl)
            (step t1.t3 (cl (= (P x) (P b))) :rule trans :premises (t1.t2 t1.t1))
            (step t1 (cl (= (let ((x a)) (P x)) (P b))) :rule let)": true,

            "(anchor :step t1 :args ((z U) (:= (x U) z)))
            (step t1.t1 (cl (= (P x) (P z))) :rule refl)
            (step t1 (cl (= (forall ((x U)) (P x)) (forall ((z U)) (P z)))) :rule bind)": true,

            "(anchor :step t1 :args ((x U) (:= (x U) x)))
            (step t1.t1 (cl (= (P x) (P x))) :rule refl)
            (step t1 (cl (= (forall ((x U)) (P x)) (forall ((x U)) (P x)))) :rule bind)": true,

            "(anchor :step t1 :args ((:= (x U) (choice ((x U)) (P x)))))
            (step t1.t1 (cl (= (P x) (P (choice ((x U)) (P x))))) :rule refl)
            (step t1 (cl (= (exists ((x U)) (P x)) (P (choice ((x U)) (P x))))) :rule sko_ex)": true,

            "(anchor :step t1 :args ((:= (x U) b)))
            (anchor :step t1.t1 :args ((z U) (:= (w U) z)))
            (step t1.t1.t1 (cl (= (Q w x) (Q z b))) :rule refl)
            (step t1.t1 (cl (= (forall ((w U)) (Q w x)) (forall ((z U)) (Q z b)))) :rule bind)
            (step t1 (cl (= (let ((x b)) (forall ((w U)) (Q w x))) (forall ((z U)) (Q z b)))) :rule let)": true,
        }
    }
}

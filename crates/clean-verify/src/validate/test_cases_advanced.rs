// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-validation test cases: advanced error cases, additional type
//! checking, and extended should-fail patterns.
//!
//! Earlier test cases are in `test_cases.rs` (type inference) and
//! `test_cases_def_eq.rs` (definitional equality).

use super::{CrossValidator, TestCase};

impl<'a> CrossValidator<'a> {
    /// Advanced error, type checking, and should-fail test cases.
    pub(super) fn generate_advanced_test_cases(&self) -> Vec<TestCase> {
        vec![
            // =====================================================================
            // MORE SHOULD FAIL CASES (N=142)
            // =====================================================================
            // Arity mismatch in application
            TestCase::ShouldFail("fun (f : Type) => f Type".to_string()),
            // Double application of non-function
            TestCase::ShouldFail("fun (A : Type) (x : A) => x x x".to_string()),
            // Bad let annotation - function type on non-function
            TestCase::ShouldFail("let f : Type -> Type := Prop in f".to_string()),
            // Higher-order type error
            TestCase::ShouldFail("fun (F : Type -> Type) (x : F) => x".to_string()),
            // =====================================================================
            // TYPE CHECK EXPANSIONS (N=142)
            // =====================================================================
            // Dependent sigma eliminator type
            TestCase::TypeCheck(
                "fun (A : Type) (B : A -> Type) (p : (C : Type) -> ((x : A) -> B x -> C) -> C) (C : Type) (f : (x : A) -> B x -> C) => p C f".to_string(),
                "(A : Type) -> (B : A -> Type) -> ((C : Type) -> ((x : A) -> B x -> C) -> C) -> (C : Type) -> ((x : A) -> B x -> C) -> C".to_string()
            ),
            // Apply polymorphic function twice
            TestCase::TypeCheck(
                "fun (id : (A : Type) -> A -> A) (B : Type) (x : B) => id B (id B x)".to_string(),
                "((A : Type) -> A -> A) -> (B : Type) -> B -> B".to_string()
            ),
            // Church numeral application
            TestCase::TypeCheck(
                "fun (n : (A : Type) -> (A -> A) -> A -> A) (B : Type) (f : B -> B) (x : B) => n B f (n B f x)".to_string(),
                "((A : Type) -> (A -> A) -> A -> A) -> (B : Type) -> (B -> B) -> B -> B".to_string()
            ),
            // =====================================================================
            // PROP-SPECIFIC TESTS (N=142)
            // Impredicativity and proof-irrelevance patterns
            // =====================================================================
            // Impredicative Prop: forall over large type into Prop stays in Prop
            TestCase::TypeInfer("(A : Type) -> (P : A -> Prop) -> Prop".to_string()),
            // Nested Prop quantification
            TestCase::TypeInfer("(P : Prop) -> (Q : Prop) -> (R : Prop) -> (P -> Q) -> (Q -> R) -> P -> R".to_string()),
            // Prop modus ponens type
            TestCase::TypeInfer("fun (P : Prop) (Q : Prop) (pq : P -> Q) (p : P) => pq p".to_string()),
            // Proof of conjunction (Church encoding)
            TestCase::TypeInfer(
                "fun (P : Prop) (Q : Prop) (p : P) (q : Q) (C : Prop) (f : P -> Q -> C) => f p q".to_string()
            ),
            // =====================================================================
            // COMPLEX DEPENDENT TYPE PATTERNS (N=142)
            // =====================================================================
            // Sigma type projector pattern
            TestCase::TypeInfer(
                "fun (A : Type) (B : A -> Type) (pair : (C : Type) -> ((x : A) -> B x -> C) -> C) => pair A (fun (x : A) (y : B x) => x)".to_string()
            ),
            // Transport/subst pattern
            TestCase::TypeInfer(
                "fun (A : Type) (x : A) (y : A) (P : A -> Type) (eq : (Q : A -> Type) -> Q x -> Q y) (px : P x) => eq P px".to_string()
            ),
            // Dependent elimination pattern
            TestCase::TypeInfer(
                "(A : Type) -> (B : A -> Type) -> (C : (x : A) -> B x -> Type) -> (x : A) -> (y : B x) -> C x y".to_string()
            ),
            // Vector-like indexed type pattern
            TestCase::TypeInfer(
                "(A : Type) -> (n : (N : Type) -> (N -> N) -> N -> N) -> Type".to_string()
            ),
            // =====================================================================
            // MONAD/FUNCTOR LAW-STYLE PATTERNS (N=145)
            // Verifying combinator laws structurally
            // =====================================================================
            // Functor identity law pattern
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (map : (A : Type) -> (B : Type) -> (A -> B) -> F A -> F B) (A : Type) (fa : F A) => map A A (fun (x : A) => x) fa".to_string()
            ),
            // Functor composition law pattern
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (map : (A : Type) -> (B : Type) -> (A -> B) -> F A -> F B) (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C) (fa : F A) => map B C g (map A B f fa)".to_string()
            ),
            // Monad return-bind law pattern (left identity)
            TestCase::TypeInfer(
                "fun (M : Type -> Type) (pure : (A : Type) -> A -> M A) (bind : (A : Type) -> (B : Type) -> M A -> (A -> M B) -> M B) (A : Type) (B : Type) (a : A) (f : A -> M B) => bind A B (pure A a) f".to_string()
            ),
            // Monad bind-return law pattern (right identity)
            TestCase::TypeInfer(
                "fun (M : Type -> Type) (pure : (A : Type) -> A -> M A) (bind : (A : Type) -> (B : Type) -> M A -> (A -> M B) -> M B) (A : Type) (ma : M A) => bind A A ma (pure A)".to_string()
            ),
            // Monad associativity law pattern
            TestCase::TypeInfer(
                "fun (M : Type -> Type) (bind : (A : Type) -> (B : Type) -> M A -> (A -> M B) -> M B) (A : Type) (B : Type) (C : Type) (ma : M A) (f : A -> M B) (g : B -> M C) => bind B C (bind A B ma f) g".to_string()
            ),
            // =====================================================================
            // COMONAD PATTERNS (N=145)
            // =====================================================================
            // Comonad extract type
            TestCase::TypeInfer(
                "fun (W : Type -> Type) (extract : (A : Type) -> W A -> A) (A : Type) (wa : W A) => extract A wa".to_string()
            ),
            // Comonad duplicate type
            TestCase::TypeInfer(
                "fun (W : Type -> Type) (duplicate : (A : Type) -> W A -> W (W A)) (A : Type) (wa : W A) => duplicate A wa".to_string()
            ),
            // Comonad extend pattern
            TestCase::TypeInfer(
                "fun (W : Type -> Type) (extend : (A : Type) -> (B : Type) -> (W A -> B) -> W A -> W B) (A : Type) (B : Type) (f : W A -> B) (wa : W A) => extend A B f wa".to_string()
            ),
            // =====================================================================
            // CATEGORY-THEORETIC PATTERNS (N=145)
            // =====================================================================
            // Category identity morphism
            TestCase::TypeInfer(
                "fun (Obj : Type) (Hom : Obj -> Obj -> Type) (id : (A : Obj) -> Hom A A) (A : Obj) => id A".to_string()
            ),
            // Category composition
            TestCase::TypeInfer(
                "fun (Obj : Type) (Hom : Obj -> Obj -> Type) (comp : (A : Obj) -> (B : Obj) -> (C : Obj) -> Hom B C -> Hom A B -> Hom A C) (A : Obj) (B : Obj) (C : Obj) (g : Hom B C) (f : Hom A B) => comp A B C g f".to_string()
            ),
            // Natural transformation type
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (G : Type -> Type) => (A : Type) -> F A -> G A".to_string()
            ),
            // Natural transformation composition
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (G : Type -> Type) (H : Type -> Type) (alpha : (A : Type) -> F A -> G A) (beta : (A : Type) -> G A -> H A) (A : Type) (fa : F A) => beta A (alpha A fa)".to_string()
            ),
            // =====================================================================
            // ADJUNCTION PATTERNS (N=145)
            // =====================================================================
            // Adjunction unit type
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (G : Type -> Type) (unit : (A : Type) -> A -> G (F A)) (A : Type) (a : A) => unit A a".to_string()
            ),
            // Adjunction counit type
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (G : Type -> Type) (counit : (A : Type) -> F (G A) -> A) (A : Type) (fga : F (G A)) => counit A fga".to_string()
            ),
            // =====================================================================
            // RECURSION SCHEME PATTERNS (N=145)
            // =====================================================================
            // Catamorphism type (fold)
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (fix : Type) (cata : (A : Type) -> (F A -> A) -> fix -> A) (A : Type) (alg : F A -> A) (x : fix) => cata A alg x".to_string()
            ),
            // Anamorphism type (unfold)
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (fix : Type) (ana : (A : Type) -> (A -> F A) -> A -> fix) (A : Type) (coalg : A -> F A) (seed : A) => ana A coalg seed".to_string()
            ),
            // Hylomorphism type (refold)
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (hylo : (A : Type) -> (B : Type) -> (F B -> B) -> (A -> F A) -> A -> B) (A : Type) (B : Type) (alg : F B -> B) (coalg : A -> F A) (seed : A) => hylo A B alg coalg seed".to_string()
            ),
            // =====================================================================
            // INDEXED FAMILY PATTERNS (N=145)
            // =====================================================================
            // Indexed function family
            TestCase::TypeInfer(
                "(I : Type) -> (A : I -> Type) -> (i : I) -> A i -> A i".to_string()
            ),
            // Indexed dependent product
            TestCase::TypeInfer(
                "(I : Type) -> (A : I -> Type) -> (B : (i : I) -> A i -> Type) -> (i : I) -> (a : A i) -> B i a".to_string()
            ),
            // Indexed type constructor application
            TestCase::TypeInfer(
                "fun (I : Type) (F : I -> Type -> Type) (i : I) (A : Type) (fa : F i A) => fa".to_string()
            ),
            // =====================================================================
            // HIGHER-KINDED POLYMORPHISM PATTERNS (N=145)
            // =====================================================================
            // Rank-2 polymorphism
            TestCase::TypeInfer(
                "fun (f : (A : Type) -> (B : Type) -> (A -> B) -> A -> B) (C : Type) (D : Type) (g : C -> D) (c : C) => f C D g c".to_string()
            ),
            // Rank-2 type-level function
            TestCase::TypeInfer(
                "fun (f : (F : Type -> Type) -> (A : Type) -> F A -> F A) (G : Type -> Type) (B : Type) (gb : G B) => f G B gb".to_string()
            ),
            // Polymorphic lens getter type
            TestCase::TypeInfer(
                "fun (s : Type) (a : Type) (get : s -> a) (x : s) => get x".to_string()
            ),
            // Polymorphic lens setter type
            TestCase::TypeInfer(
                "fun (s : Type) (a : Type) (set : s -> a -> s) (x : s) (v : a) => set x v".to_string()
            ),
            // =====================================================================
            // EXISTENTIAL TYPE PATTERNS (N=145)
            // =====================================================================
            // Existential introduction (pack)
            TestCase::TypeInfer(
                "fun (R : Type) (A : Type) (witness : A) (pack : (B : Type) -> B -> R) => pack A witness".to_string()
            ),
            // Existential elimination (unpack)
            TestCase::TypeInfer(
                "fun (Exists : Type) (R : Type) (unpack : Exists -> (A : Type) -> (A -> R) -> R) (e : Exists) (B : Type) (use : B -> R) => unpack e B use".to_string()
            ),
            // =====================================================================
            // CONTINUATION MONAD PATTERNS (N=145)
            // =====================================================================
            // Cont return
            TestCase::TypeInfer(
                "fun (R : Type) (A : Type) (a : A) => fun (k : A -> R) => k a".to_string()
            ),
            // Cont bind
            TestCase::TypeInfer(
                "fun (R : Type) (A : Type) (B : Type) (ma : (A -> R) -> R) (f : A -> (B -> R) -> R) => fun (k : B -> R) => ma (fun (a : A) => f a k)".to_string()
            ),
            // Cont callCC type
            TestCase::TypeInfer(
                "fun (R : Type) (A : Type) (f : ((A -> (B : Type) -> (B -> R) -> R) -> (A -> R) -> R) -> (A -> R) -> R) (k : A -> R) => f (fun (exit : A -> (B : Type) -> (B -> R) -> R) => fun (k2 : A -> R) => k2) k".to_string()
            ),
            // =====================================================================
            // STATE MONAD PATTERNS (N=145)
            // =====================================================================
            // State type (S -> (A, S) encoded)
            TestCase::TypeInfer(
                "fun (S : Type) (A : Type) => S -> (R : Type) -> (A -> S -> R) -> R".to_string()
            ),
            // State get
            TestCase::TypeInfer(
                "fun (S : Type) (s : S) (R : Type) (k : S -> S -> R) => k s s".to_string()
            ),
            // State put
            TestCase::TypeInfer(
                "fun (S : Type) (newS : S) (oldS : S) (R : Type) (k : S -> R) => k newS".to_string()
            ),
            // =====================================================================
            // READER MONAD PATTERNS (N=145)
            // =====================================================================
            // Reader return
            TestCase::TypeInfer(
                "fun (R : Type) (A : Type) (a : A) (env : R) => a".to_string()
            ),
            // Reader ask
            TestCase::TypeInfer(
                "fun (R : Type) (env : R) => env".to_string()
            ),
            // Reader local
            TestCase::TypeInfer(
                "fun (R : Type) (A : Type) (f : R -> R) (ma : R -> A) (env : R) => ma (f env)".to_string()
            ),
            // =====================================================================
            // WRITER MONAD PATTERNS (N=145)
            // =====================================================================
            // Writer type (Church-encoded (A, W))
            TestCase::TypeInfer(
                "fun (W : Type) (A : Type) (a : A) (w : W) (R : Type) (k : A -> W -> R) => k a w".to_string()
            ),
            // Writer tell
            TestCase::TypeInfer(
                "fun (W : Type) (w : W) (Unit : Type) (unit : Unit) (R : Type) (k : Unit -> W -> R) => k unit w".to_string()
            ),
            // =====================================================================
            // FREE MONAD PATTERNS (N=145)
            // =====================================================================
            // Free Pure type
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (A : Type) (a : A) (R : Type) (pureCase : A -> R) (freeCase : F R -> R) => pureCase a".to_string()
            ),
            // Free Wrap type
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (A : Type) (fa : F ((R : Type) -> (A -> R) -> (F R -> R) -> R)) (R : Type) (pureCase : A -> R) (freeCase : F R -> R) => fa".to_string()
            ),
            // =====================================================================
            // YONEDA LEMMA PATTERNS (N=145)
            // =====================================================================
            // Yoneda embedding type
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (A : Type) => (B : Type) -> (A -> B) -> F B".to_string()
            ),
            // Yoneda lower (run)
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (A : Type) (y : (B : Type) -> (A -> B) -> F B) => y A (fun (a : A) => a)".to_string()
            ),
            // Coyoneda type
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (A : Type) (B : Type) (fb : F B) (f : B -> A) (C : Type) (k : (D : Type) -> F D -> (D -> A) -> C) => k B fb f".to_string()
            ),
            // =====================================================================
            // ADDITIONAL DEFEQ TESTS (N=145)
            // =====================================================================
            // Beta reduction chain
            TestCase::DefEq(
                "fun (A : Type) (x : A) => (fun (y : A) => (fun (z : A) => z) y) x".to_string(),
                "fun (A : Type) (x : A) => x".to_string()
            ),
            // Let chain reduction
            TestCase::DefEq(
                "let a : Type := Type in let b : a := Prop in let c : b := Prop in c".to_string(),
                "Prop".to_string()
            ),
            // Polymorphic identity applied is identity
            TestCase::DefEq(
                "fun (A : Type) (x : A) => (fun (B : Type) (y : B) => y) A ((fun (C : Type) (z : C) => z) A x)".to_string(),
                "fun (A : Type) (x : A) => x".to_string()
            ),
            // Const K applied twice
            TestCase::DefEq(
                "fun (A : Type) (x : A) (y : A) => (fun (B : Type) (C : Type) (a : B) (b : C) => a) A A x y".to_string(),
                "fun (A : Type) (x : A) (y : A) => x".to_string()
            ),
            // Arrow type via forall syntax reflexivity
            TestCase::DefEq(
                "forall (A : Type) (B : Type), A -> B -> A".to_string(),
                "forall (A : Type) (B : Type), A -> B -> A".to_string()
            ),
            // =====================================================================
            // ADDITIONAL NOT DEFEQ TESTS (N=145)
            // =====================================================================
            // Different monadic structure
            TestCase::NotDefEq(
                "fun (A : Type) (x : A) (y : A) => x".to_string(),
                "fun (A : Type) (x : A) (y : A) => (fun (z : A) => y) x".to_string()
            ),
            // Type vs Prop in result
            TestCase::NotDefEq(
                "fun (A : Type) => Type".to_string(),
                "fun (A : Type) => Prop".to_string()
            ),
            // Different fixed point structure
            TestCase::NotDefEq(
                "fun (A : Type) (f : A -> A) => f".to_string(),
                "fun (A : Type) (f : A -> A) => fun (x : A) => f (f x)".to_string()
            ),
            // =====================================================================
            // ADDITIONAL TYPE CHECK TESTS (N=145)
            // =====================================================================
            // Functor map type check
            TestCase::TypeCheck(
                "fun (F : Type -> Type) (map : (A : Type) -> (B : Type) -> (A -> B) -> F A -> F B) (A : Type) (B : Type) (f : A -> B) (fa : F A) => map A B f fa".to_string(),
                "(F : Type -> Type) -> ((A : Type) -> (B : Type) -> (A -> B) -> F A -> F B) -> (A : Type) -> (B : Type) -> (A -> B) -> F A -> F B".to_string()
            ),
            // Monad bind type check
            TestCase::TypeCheck(
                "fun (M : Type -> Type) (bind : (A : Type) -> (B : Type) -> M A -> (A -> M B) -> M B) (A : Type) (B : Type) (ma : M A) (f : A -> M B) => bind A B ma f".to_string(),
                "(M : Type -> Type) -> ((A : Type) -> (B : Type) -> M A -> (A -> M B) -> M B) -> (A : Type) -> (B : Type) -> M A -> (A -> M B) -> M B".to_string()
            ),
            // Natural transformation type check
            TestCase::TypeCheck(
                "fun (F : Type -> Type) (G : Type -> Type) (nat : (A : Type) -> F A -> G A) (A : Type) (fa : F A) => nat A fa".to_string(),
                "(F : Type -> Type) -> (G : Type -> Type) -> ((A : Type) -> F A -> G A) -> (A : Type) -> F A -> G A".to_string()
            ),
            // Continuation type check
            TestCase::TypeCheck(
                "fun (R : Type) (A : Type) (a : A) (k : A -> R) => k a".to_string(),
                "(R : Type) -> (A : Type) -> A -> (A -> R) -> R".to_string()
            ),
            // =====================================================================
            // ADDITIONAL SHOULD FAIL TESTS (N=145)
            // =====================================================================
            // Applying monomorphic function to wrong type
            TestCase::ShouldFail("fun (A : Type) (B : Type) (f : A -> A) (x : B) => f x".to_string()),
            // Missing intermediate type in composition
            TestCase::ShouldFail("fun (A : Type) (C : Type) (f : A -> A) (g : C -> C) (x : A) => g (f x)".to_string()),
            // Applying to partially applied function wrongly
            TestCase::ShouldFail("fun (F : Type -> Type) (x : F) => x Type".to_string()),
            // Type constructor applied to non-type
            TestCase::ShouldFail("fun (F : Type -> Type) (A : Type) (a : A) => F a".to_string()),
        ]
    }
}

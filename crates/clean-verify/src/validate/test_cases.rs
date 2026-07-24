// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-validation test cases: type inference, type checking, and basic
//! error cases (TypeInfer, TypeCheck, ShouldFail).
//!
//! DefEq and NotDefEq test cases are in `test_cases_def_eq.rs`.

use super::{CrossValidator, TestCase};

impl<'a> CrossValidator<'a> {
    /// Type inference, type checking, and basic error test cases.
    pub(super) fn generate_type_test_cases(&self) -> Vec<TestCase> {
        vec![
            // === Basic sorts ===
            TestCase::TypeInfer("Type".to_string()),
            TestCase::TypeInfer("Type -> Type".to_string()),
            TestCase::TypeInfer("(A : Type) -> A".to_string()),
            // Prop (universe 0)
            TestCase::TypeInfer("Prop".to_string()),
            TestCase::TypeInfer("Prop -> Prop".to_string()),
            // === Identity function variants ===
            TestCase::TypeInfer("fun (A : Type) (x : A) => x".to_string()),
            // Identity on Prop
            TestCase::TypeInfer("fun (P : Prop) (p : P) => p".to_string()),
            // Identity with explicit return type
            TestCase::TypeInfer("fun (A : Type) => fun (x : A) => x".to_string()),
            // === Const function variants ===
            TestCase::TypeInfer("fun (A : Type) (B : Type) (a : A) (b : B) => a".to_string()),
            TestCase::TypeInfer("fun (A : Type) (B : Type) (a : A) (b : B) => b".to_string()),
            // Flip (K combinator variant)
            TestCase::TypeInfer("fun (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (b : B) (a : A) => f a b".to_string()),
            // === Application patterns ===
            TestCase::TypeInfer("fun (A : Type) (f : A -> A) (x : A) => f x".to_string()),
            // Double application
            TestCase::TypeInfer("fun (A : Type) (f : A -> A) (x : A) => f (f x)".to_string()),
            // Triple application
            TestCase::TypeInfer("fun (A : Type) (f : A -> A) (x : A) => f (f (f x))".to_string()),
            // === Nested lambdas ===
            TestCase::TypeInfer("fun (A : Type) => fun (B : Type) => fun (x : A) => x".to_string()),
            // Deeply nested
            TestCase::TypeInfer("fun (A : Type) => fun (B : Type) => fun (C : Type) => fun (x : A) => x".to_string()),
            // === Pi types ===
            TestCase::TypeInfer("(A : Type) -> (B : Type) -> A -> B -> A".to_string()),
            // Dependent Pi
            TestCase::TypeInfer("(A : Type) -> (B : A -> Type) -> (x : A) -> B x".to_string()),
            // Nested Pi
            TestCase::TypeInfer("(A : Type) -> (B : Type) -> (C : Type) -> A -> B -> C -> A".to_string()),
            // === Higher-order functions ===
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (C : Type) (g : B -> C) (f : A -> B) (x : A) => g (f x)".to_string()
            ),
            // S combinator
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (C : Type) (x : A -> B -> C) (y : A -> B) (z : A) => x z (y z)".to_string()
            ),
            // === Church numerals ===
            // Church numeral type
            TestCase::TypeInfer("(A : Type) -> (A -> A) -> A -> A".to_string()),
            // Church zero
            TestCase::TypeInfer("fun (A : Type) (f : A -> A) (x : A) => x".to_string()),
            // Church one
            TestCase::TypeInfer("fun (A : Type) (f : A -> A) (x : A) => f x".to_string()),
            // Church two
            TestCase::TypeInfer("fun (A : Type) (f : A -> A) (x : A) => f (f x)".to_string()),
            // Church successor
            TestCase::TypeInfer(
                "fun (n : (A : Type) -> (A -> A) -> A -> A) (A : Type) (f : A -> A) (x : A) => f (n A f x)".to_string()
            ),
            // Church addition
            TestCase::TypeInfer(
                "fun (m : (A : Type) -> (A -> A) -> A -> A) (n : (A : Type) -> (A -> A) -> A -> A) (A : Type) (f : A -> A) (x : A) => m A f (n A f x)".to_string()
            ),
            // === Church booleans ===
            // Church true
            TestCase::TypeInfer("fun (A : Type) (t : A) (f : A) => t".to_string()),
            // Church false
            TestCase::TypeInfer("fun (A : Type) (t : A) (f : A) => f".to_string()),
            // Church and
            TestCase::TypeInfer(
                "fun (p : (A : Type) -> A -> A -> A) (q : (A : Type) -> A -> A -> A) (A : Type) (t : A) (f : A) => p A (q A t f) f".to_string()
            ),
            // === Polymorphic functions ===
            // Polymorphic identity application
            TestCase::TypeInfer("fun (A : Type) (B : Type) (f : (C : Type) -> C -> C) (x : A) => f A x".to_string()),
            // Partial polymorphic application
            TestCase::TypeInfer("fun (f : (A : Type) -> A -> A) (B : Type) => f B".to_string()),
            // === Let bindings ===
            TestCase::TypeInfer("let x : Type := Type in x".to_string()),
            TestCase::TypeInfer("let id : (A : Type) -> A -> A := fun (A : Type) (x : A) => x in id".to_string()),
            // Nested let
            TestCase::TypeInfer("let A : Type := Type in let x : A := Type in x".to_string()),
            // Let with dependent application
            TestCase::TypeInfer(
                "let apply : (A : Type) -> (A -> A) -> A -> A := fun (A : Type) (f : A -> A) (x : A) => f x in apply".to_string()
            ),
            // Let with polymorphic specialization
            TestCase::TypeInfer(
                "let apply : (A : Type) -> (A -> A) -> A -> A := fun (A : Type) (f : A -> A) (x : A) => f x in fun (B : Type) (g : B -> B) (b : B) => apply B g b".to_string()
            ),
            // === Type-level functions ===
            // Type constructor
            TestCase::TypeInfer("fun (F : Type -> Type) (A : Type) => F A".to_string()),
            // Higher-kinded type
            TestCase::TypeInfer("fun (F : Type -> Type) (G : Type -> Type) (A : Type) => F (G A)".to_string()),
            // Higher-order type constructor application
            TestCase::TypeInfer(
                "fun (F : (Type -> Type) -> Type) (G : Type -> Type) => F G".to_string()
            ),
            // === Church multiplication ===
            TestCase::TypeInfer(
                "fun (m : (A : Type) -> (A -> A) -> A -> A) (n : (A : Type) -> (A -> A) -> A -> A) (A : Type) (f : A -> A) => m A (n A f)".to_string()
            ),
            // === Church or ===
            TestCase::TypeInfer(
                "fun (p : (A : Type) -> A -> A -> A) (q : (A : Type) -> A -> A -> A) (A : Type) (t : A) (f : A) => p A t (q A t f)".to_string()
            ),
            // === Church not ===
            TestCase::TypeInfer(
                "fun (p : (A : Type) -> A -> A -> A) (A : Type) (t : A) (f : A) => p A f t".to_string()
            ),
            // === Church if-then-else ===
            TestCase::TypeInfer(
                "fun (p : (A : Type) -> A -> A -> A) (A : Type) (then_ : A) (else_ : A) => p A then_ else_".to_string()
            ),
            // === Church pairs ===
            // Pair constructor
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (a : A) (b : B) (f : A -> B -> A) => f a b".to_string()
            ),
            // === Dependent function types ===
            // Dependent elimination
            TestCase::TypeInfer("(P : Prop -> Type) -> (h : (Q : Prop) -> P Q) -> P Prop".to_string()),
            // Impredicative Prop
            TestCase::TypeInfer("(P : Prop) -> (Q : Prop) -> P -> Q -> P".to_string()),
            TestCase::TypeInfer("(P : Prop) -> (Q : Prop) -> (P -> Q) -> P -> Q".to_string()),
            // === Universe polymorphism patterns ===
            // Type of types
            TestCase::TypeInfer("Type -> Type -> Type".to_string()),
            // Nested sorts
            TestCase::TypeInfer("(A : Type) -> (B : Type) -> Type".to_string()),
            // === Currying / uncurrying patterns ===
            // Curry
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (C : Type) (f : (A -> B) -> C) (a : A) (g : B -> C) => g (f (fun (x : A) => f (fun (y : A) => y)))".to_string()
            ),
            // === Continuation passing style ===
            // CPS identity
            TestCase::TypeInfer("fun (A : Type) (R : Type) (a : A) (k : A -> R) => k a".to_string()),
            // CPS composition
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (C : Type) (R : Type) (f : A -> (B -> R) -> R) (g : B -> (C -> R) -> R) (a : A) (k : C -> R) => f a (fun (b : B) => g b k)".to_string()
            ),
            // === Fixed-point combinator types ===
            // Y combinator type (not the combinator itself, just its type)
            TestCase::TypeInfer("((A : Type) -> (A -> A) -> A) -> Type".to_string()),
            // === Deep nesting stress test ===
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (a : A) => a".to_string()
            ),
            // === Let with dependent types ===
            TestCase::TypeInfer("let F : Type -> Type := fun (A : Type) => A -> A in F".to_string()),
            TestCase::TypeInfer("let F : Type -> Type := fun (A : Type) => A -> A in let x : F Type := fun (A : Type) => A in x".to_string()),
            // === Shadowing ===
            TestCase::TypeInfer("fun (A : Type) (A : A) => A".to_string()),
            TestCase::TypeInfer("fun (x : Type) (x : x) => x".to_string()),
            // === Type annotation patterns ===
            TestCase::TypeInfer("(fun (A : Type) (x : A) => x : (A : Type) -> A -> A)".to_string()),
            // === Invalid cases (should error in both spec and impl) ===
            TestCase::ShouldFail("x".to_string()), // Unbound variable
            TestCase::ShouldFail("fun x => x".to_string()), // Missing type annotation
            TestCase::ShouldFail("Type Type".to_string()), // Type is not a function
            TestCase::ShouldFail("fun (x : Type) => x x".to_string()), // Self-application type error
            TestCase::ShouldFail("fun (A : Type) (x : A) => x A".to_string()), // Applying value to type
            // More invalid cases
            TestCase::ShouldFail("fun (A : Type) => A A".to_string()), // A is not a function type
            TestCase::ShouldFail("fun (f : Type -> Type) => f f".to_string()), // Type mismatch in application
            TestCase::ShouldFail("let x : Prop := Type in x".to_string()), // Universe mismatch
            // === TypeCheck test cases ===
            // Verify expression has expected type
            TestCase::TypeCheck("Type".to_string(), "Type".to_string()),
            TestCase::TypeCheck("Prop".to_string(), "Type".to_string()),
            TestCase::TypeCheck(
                "fun (A : Type) (x : A) => x".to_string(),
                "(A : Type) -> A -> A".to_string(),
            ),
            // Church numeral type check
            TestCase::TypeCheck(
                "fun (A : Type) (f : A -> A) (x : A) => x".to_string(),
                "(A : Type) -> (A -> A) -> A -> A".to_string(),
            ),
            // Const function
            TestCase::TypeCheck(
                "fun (A : Type) (B : Type) (a : A) (b : B) => a".to_string(),
                "(A : Type) -> (B : Type) -> A -> B -> A".to_string(),
            ),
            // Composition type check
            TestCase::TypeCheck(
                "fun (A : Type) (B : Type) (C : Type) (g : B -> C) (f : A -> B) (x : A) => g (f x)".to_string(),
                "(A : Type) -> (B : Type) -> (C : Type) -> (B -> C) -> (A -> B) -> A -> C".to_string(),
            ),
            // === W combinator (duplicate arguments) ===
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (f : A -> A -> B) (x : A) => f x x".to_string()
            ),
            // === B combinator (function composition) ===
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (C : Type) (f : B -> C) (g : A -> B) (x : A) => f (g x)".to_string()
            ),
            // === C combinator (flip) ===
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (y : B) (x : A) => f x y".to_string()
            ),
            // === I* combinator (apply identity to function) ===
            TestCase::TypeInfer(
                "fun (A : Type) (B : Type) (f : A -> B) (x : A) => f x".to_string()
            ),
            // === Polymorphic const ===
            TestCase::TypeInfer(
                "fun (A : Type) (a : A) (B : Type) => a".to_string()
            ),
            // === Church numeral exponentiation type ===
            TestCase::TypeInfer(
                "fun (m : (A : Type) -> (A -> A) -> A -> A) (n : (A : Type) -> (A -> A) -> A -> A) (A : Type) (f : A -> A) => n (A -> A) (m A) f".to_string()
            ),
            // === Nested dependent types ===
            TestCase::TypeInfer(
                "(A : Type) -> (B : A -> Type) -> (C : (x : A) -> B x -> Type) -> Type".to_string()
            ),
            // === Triple nested dependent ===
            TestCase::TypeInfer(
                "(A : Type) -> (B : A -> Type) -> (C : (x : A) -> B x -> Type) -> (x : A) -> (y : B x) -> C x y".to_string()
            ),
            // === Leibniz equality type ===
            TestCase::TypeInfer(
                "(A : Type) -> A -> A -> Type".to_string()
            ),
            // === Leibniz refl pattern ===
            TestCase::TypeInfer(
                "fun (A : Type) (x : A) (P : A -> Type) (px : P x) => px".to_string()
            ),
            // === Transport (subst) pattern ===
            TestCase::TypeInfer(
                "fun (A : Type) (P : A -> Type) (x : A) (y : A) (eq : (Q : A -> Type) -> Q x -> Q y) (px : P x) => eq P px".to_string()
            ),
            // === Functor-like map pattern ===
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (A : Type) (B : Type) (f : A -> B) (fa : F A) => fa".to_string()
            ),
            // === Higher-rank polymorphism ===
            TestCase::TypeInfer(
                "fun (f : (A : Type) -> A -> A) (B : Type) (x : B) => f B x".to_string()
            ),
            // === System F style encoding ===
            TestCase::TypeInfer(
                "fun (X : Type) (wrap : (A : Type) -> A -> X) (unwrap : X -> (A : Type) -> A) => wrap".to_string()
            ),
            // === More error cases ===
            // Applying non-function
            TestCase::ShouldFail("fun (x : Type) (y : x) => y x".to_string()),
            // Type mismatch in let
            TestCase::ShouldFail("let id : Type -> Type := fun (A : Type) (x : A) => x in id".to_string()),
            // Wrong kind application
            TestCase::ShouldFail("(fun (A : Type) => A) Type Type".to_string()),
            // Dependent argument mismatch
            TestCase::ShouldFail("fun (A : Type) (p : A -> Prop) (x : Prop) => p x".to_string()),
            // Ill-typed let binding annotation
            TestCase::ShouldFail("let bad : Type := fun (A : Type) => A in bad".to_string()),
            // Applying non-function value
            TestCase::ShouldFail("fun (A : Type) (x : A) => x x".to_string()),
            // === Universe level specific tests ===
            // Type in Type (universe polymorphism)
            TestCase::TypeInfer("fun (U : Type) (A : U) => A".to_string()),
            // Prop is a subtype of Type
            TestCase::TypeInfer("fun (P : Prop) => P".to_string()),
            // Impredicative Prop (forall over Prop stays in Prop)
            TestCase::TypeInfer("(P : Prop) -> P".to_string()),
            // Predicative Type (forall over Type goes up)
            TestCase::TypeInfer("(A : Type) -> A".to_string()),
            // === Natural number patterns (without inductive) ===
            // Nat-like type via Church encoding
            TestCase::TypeInfer("(N : Type) -> (N -> N) -> N -> N".to_string()),
            // Nat-like zero
            TestCase::TypeInfer("fun (N : Type) (s : N -> N) (z : N) => z".to_string()),
            // Nat-like succ
            TestCase::TypeInfer("fun (n : (N : Type) -> (N -> N) -> N -> N) (N : Type) (s : N -> N) (z : N) => s (n N s z)".to_string()),
            // === Optional/Maybe pattern ===
            // Maybe type via Church encoding
            TestCase::TypeInfer("(A : Type) -> (R : Type) -> (A -> R) -> R -> R".to_string()),
            // Just
            TestCase::TypeInfer("fun (A : Type) (a : A) (R : Type) (f : A -> R) (r : R) => f a".to_string()),
            // Nothing
            TestCase::TypeInfer("fun (A : Type) (R : Type) (f : A -> R) (r : R) => r".to_string()),
            // === Either/Sum pattern ===
            // Either type
            TestCase::TypeInfer("(A : Type) -> (B : Type) -> (R : Type) -> (A -> R) -> (B -> R) -> R".to_string()),
            // Left
            TestCase::TypeInfer("fun (A : Type) (B : Type) (a : A) (R : Type) (l : A -> R) (r : B -> R) => l a".to_string()),
            // Right
            TestCase::TypeInfer("fun (A : Type) (B : Type) (b : B) (R : Type) (l : A -> R) (r : B -> R) => r b".to_string()),
            // === Product/Pair pattern ===
            // Product type
            TestCase::TypeInfer("(A : Type) -> (B : Type) -> (R : Type) -> (A -> B -> R) -> R".to_string()),
            // Pair constructor
            TestCase::TypeInfer("fun (A : Type) (B : Type) (a : A) (b : B) (R : Type) (f : A -> B -> R) => f a b".to_string()),
            // Fst projection
            TestCase::TypeInfer("fun (A : Type) (B : Type) (p : (R : Type) -> (A -> B -> R) -> R) => p A (fun (a : A) (b : B) => a)".to_string()),
            // Snd projection
            TestCase::TypeInfer("fun (A : Type) (B : Type) (p : (R : Type) -> (A -> B -> R) -> R) => p B (fun (a : A) (b : B) => b)".to_string()),
            // === ListType pattern ===
            // ListType type via Church encoding
            TestCase::TypeInfer("(A : Type) -> (R : Type) -> (A -> R -> R) -> R -> R".to_string()),
            // Nil
            TestCase::TypeInfer("fun (A : Type) (R : Type) (c : A -> R -> R) (n : R) => n".to_string()),
            // Cons
            TestCase::TypeInfer("fun (A : Type) (x : A) (xs : (R : Type) -> (A -> R -> R) -> R -> R) (R : Type) (c : A -> R -> R) (n : R) => c x (xs R c n)".to_string()),
            // === Monad-like bind pattern ===
            TestCase::TypeInfer(
                "fun (M : Type -> Type) (A : Type) (B : Type) (ma : M A) (f : A -> M B) => ma".to_string()
            ),
            // === Applicative-like pure pattern ===
            TestCase::TypeInfer(
                "fun (F : Type -> Type) (A : Type) (a : A) (pure : (B : Type) -> B -> F B) => pure A a".to_string()
            ),
            // === Fixed-point operator type (Curry's Y) ===
            // Note: Can't express Y itself without recursion, but can express its type
            TestCase::TypeInfer("(A : Type) -> ((A -> A) -> A) -> A".to_string()),
            // === Recursive type pattern (F-algebra) ===
            TestCase::TypeInfer("(F : Type -> Type) -> ((A : Type) -> F A -> A) -> Type".to_string()),
            // === Dependent Prop patterns ===
            TestCase::TypeInfer("fun (A : Type) (p : A -> Prop) (x : A) => p x".to_string()),
            TestCase::TypeInfer("(A : Type) -> (p : A -> Prop) -> A -> Prop".to_string()),
            TestCase::TypeInfer("forall (A : Type) (P : A -> Prop), A -> Prop".to_string()),
            TestCase::TypeInfer("fun (P : Prop) (Q : Prop) (h : P -> Q) (p : P) => h p".to_string()),
            // Nested lets returning the bound value
            TestCase::TypeInfer("fun (A : Type) (x : A) => let y : A := x in let z : A := y in z".to_string()),
            // Beta-reduction through type-indexed identity
            TestCase::TypeInfer("fun (A : Type) (x : A) => (fun (B : Type) (y : B) => y) A x".to_string()),
        ]
    }
}

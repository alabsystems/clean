// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-validation test cases: definitional equality, not-def-eq,
//! advanced type checking, and additional error cases.
//!
//! Type inference test cases are in `test_cases.rs`.

use super::{CrossValidator, TestCase};

impl<'a> CrossValidator<'a> {
    /// DefEq, NotDefEq, advanced TypeCheck, and additional ShouldFail test cases.
    pub(super) fn generate_def_eq_test_cases(&self) -> Vec<TestCase> {
        vec![
            // DEFINITIONAL EQUALITY TESTS
            // These test the core conversion algorithm (is_def_eq)
            // Note: Some beta/application tests are limited by universe level handling
            // in elaboration. Focus on tests that work with the current elaborator.
            // =====================================================================
            // === Reflexivity ===
            TestCase::DefEq("Type".to_string(), "Type".to_string()),
            TestCase::DefEq("Prop".to_string(), "Prop".to_string()),
            TestCase::DefEq("fun (A : Type) (x : A) => x".to_string(), "fun (A : Type) (x : A) => x".to_string()),
            // === Alpha equivalence ===
            // λA.λx.x ≡ λB.λy.y (same up to variable names)
            TestCase::DefEq(
                "fun (A : Type) (x : A) => x".to_string(),
                "fun (B : Type) (y : B) => y".to_string()
            ),
            // More complex alpha equivalence
            TestCase::DefEq(
                "fun (A : Type) (B : Type) (f : A -> B) (x : A) => f x".to_string(),
                "fun (X : Type) (Y : Type) (g : X -> Y) (a : X) => g a".to_string()
            ),
            // NOTE: "(A : Type) -> A -> A" syntax is not yet supported by the elaborator
            // for dependent Pi types. Use "forall (A : Type), A -> A" instead, or
            // test with lambda equivalence. Skipped for now.
            // === Let reduction (zeta) ===
            // let x := Prop in x ≡ Prop
            TestCase::DefEq("let x : Type := Prop in x".to_string(), "Prop".to_string()),
            // === Beta reduction in values (not involving Type as value) ===
            // These work because we're not applying Type-level functions to Type
            TestCase::DefEq(
                "fun (A : Type) (x : A) => (fun (y : A) => y) x".to_string(),
                "fun (A : Type) (x : A) => x".to_string()
            ),
            // Let with usage
            TestCase::DefEq(
                "fun (A : Type) => let B : Type := A in B".to_string(),
                "fun (A : Type) => A".to_string()
            ),
            // === Sort relationships ===
            // Prop : Type (inferring, not comparing values)
            TestCase::DefEq("Prop -> Prop".to_string(), "Prop -> Prop".to_string()),
            TestCase::DefEq("Type -> Prop".to_string(), "Type -> Prop".to_string()),
            // =====================================================================
            // NOT DEFINITIONALLY EQUAL TESTS
            // These verify that distinct expressions are not confused
            // =====================================================================
            // === Distinct sorts ===
            TestCase::NotDefEq("Type".to_string(), "Prop".to_string()),
            // === Different arities ===
            TestCase::NotDefEq(
                "fun (A : Type) (x : A) => x".to_string(),
                "fun (A : Type) (B : Type) (x : A) (y : B) => x".to_string()
            ),
            // === Structurally different - different return values ===
            TestCase::NotDefEq(
                "fun (A : Type) (x : A) => x".to_string(),
                "fun (A : Type) (x : A) => A".to_string()
            ),
            // === Different arrow arities ===
            TestCase::NotDefEq(
                "Type -> Type".to_string(),
                "Type -> Type -> Type".to_string()
            ),
            // === Different arrow domains ===
            TestCase::NotDefEq(
                "Type -> Prop".to_string(),
                "Prop -> Prop".to_string()
            ),
            // === Different arrow codomains ===
            TestCase::NotDefEq(
                "Prop -> Type".to_string(),
                "Prop -> Prop".to_string()
            ),
            // =====================================================================
            // ADDITIONAL TYPE CHECK TESTS
            // Verify more complex type relationships
            // =====================================================================
            // S combinator type check
            TestCase::TypeCheck(
                "fun (A : Type) (B : Type) (C : Type) (x : A -> B -> C) (y : A -> B) (z : A) => x z (y z)".to_string(),
                "(A : Type) -> (B : Type) -> (C : Type) -> (A -> B -> C) -> (A -> B) -> A -> C".to_string(),
            ),
            // K combinator (const) with different arg order
            TestCase::TypeCheck(
                "fun (A : Type) (B : Type) (x : A) (y : B) => x".to_string(),
                "(A : Type) -> (B : Type) -> A -> B -> A".to_string(),
            ),
            // Church successor type check
            TestCase::TypeCheck(
                "fun (n : (A : Type) -> (A -> A) -> A -> A) (A : Type) (f : A -> A) (x : A) => f (n A f x)".to_string(),
                "((A : Type) -> (A -> A) -> A -> A) -> (A : Type) -> (A -> A) -> A -> A".to_string(),
            ),
            // Higher-order function type check
            TestCase::TypeCheck(
                "fun (f : (A : Type) -> A -> A) (B : Type) (x : B) => f B x".to_string(),
                "((A : Type) -> A -> A) -> (B : Type) -> B -> B".to_string(),
            ),
            // Let binding type check
            TestCase::TypeCheck(
                "let id : (A : Type) -> A -> A := fun (A : Type) (x : A) => x in id".to_string(),
                "(A : Type) -> A -> A".to_string(),
            ),
            // Prop arrow type check
            TestCase::TypeCheck(
                "fun (P : Prop) (Q : Prop) (p : P) => p".to_string(),
                "(P : Prop) -> (Q : Prop) -> P -> P".to_string(),
            ),
            // Flip function type check
            TestCase::TypeCheck(
                "fun (A : Type) (B : Type) (C : Type) (f : A -> B -> C) (b : B) (a : A) => f a b".to_string(),
                "(A : Type) -> (B : Type) -> (C : Type) -> (A -> B -> C) -> B -> A -> C".to_string(),
            ),
            // Nested dependent type check
            TestCase::TypeCheck(
                "fun (A : Type) (B : A -> Type) (x : A) (y : B x) => y".to_string(),
                "(A : Type) -> (B : A -> Type) -> (x : A) -> B x -> B x".to_string(),
            ),
            // Dependent Prop application check
            TestCase::TypeCheck(
                "fun (A : Type) (p : A -> Prop) (x : A) => p x".to_string(),
                "(A : Type) -> (A -> Prop) -> A -> Prop".to_string(),
            ),
            // Prop implication application check
            TestCase::TypeCheck(
                "fun (P : Prop) (Q : Prop) (h : P -> Q) => fun (p : P) => h p".to_string(),
                "(P : Prop) -> (Q : Prop) -> (P -> Q) -> P -> Q".to_string(),
            ),
            // Polymorphic apply from let binding
            TestCase::TypeCheck(
                "let apply : (A : Type) -> (A -> A) -> A -> A := fun (A : Type) (f : A -> A) (x : A) => f x in fun (B : Type) (g : B -> B) (b : B) => apply B g b".to_string(),
                "(B : Type) -> (B -> B) -> B -> B".to_string(),
            ),
            // =====================================================================
            // ADDITIONAL DEFEQ TESTS
            // Test more definitional equality cases
            // =====================================================================
            // Nested let reduction
            TestCase::DefEq(
                "let x : Type := Type in let y : Type := x in y".to_string(),
                "Type".to_string()
            ),
            // Lambda with let inside
            TestCase::DefEq(
                "fun (A : Type) => let B : Type := A in B -> B".to_string(),
                "fun (A : Type) => A -> A".to_string()
            ),
            // Double let
            TestCase::DefEq(
                "let x : Type := Prop in let y : Type := Type in x".to_string(),
                "Prop".to_string()
            ),
            // Let in return position
            TestCase::DefEq(
                "fun (A : Type) (x : A) => let y : A := x in y".to_string(),
                "fun (A : Type) (x : A) => x".to_string()
            ),
            // Alpha equivalence with more variables
            TestCase::DefEq(
                "fun (A : Type) (B : Type) (C : Type) (f : A -> B) (g : B -> C) (x : A) => g (f x)".to_string(),
                "fun (X : Type) (Y : Type) (Z : Type) (h : X -> Y) (k : Y -> Z) (a : X) => k (h a)".to_string()
            ),
            // Beta in nested context
            TestCase::DefEq(
                "fun (A : Type) (B : Type) => (fun (X : Type) => X) A".to_string(),
                "fun (A : Type) (B : Type) => A".to_string()
            ),
            // Prop identity vs direct
            TestCase::DefEq(
                "fun (P : Prop) => (fun (Q : Prop) => Q) P".to_string(),
                "fun (P : Prop) => P".to_string()
            ),
            // Pi type reflexivity (using forall syntax)
            TestCase::DefEq(
                "forall (A : Type) (B : Type), A -> B -> A".to_string(),
                "forall (A : Type) (B : Type), A -> B -> A".to_string()
            ),
            // Alpha in Pi types (using forall syntax)
            TestCase::DefEq(
                "forall (A : Type), A -> A".to_string(),
                "forall (B : Type), B -> B".to_string()
            ),
            // Beta through higher-order argument
            TestCase::DefEq(
                "fun (A : Type) (x : A) => (fun (f : A -> A) => f x) (fun (z : A) => z)".to_string(),
                "fun (A : Type) (x : A) => x".to_string()
            ),
            // Nested beta reductions
            TestCase::DefEq(
                "fun (A : Type) (x : A) => (fun (y : A) => y) ((fun (z : A) => z) x)".to_string(),
                "fun (A : Type) (x : A) => x".to_string()
            ),
            // Nested lets with dependent reuse
            TestCase::DefEq(
                "fun (A : Type) (x : A) => let y : A := x in let z : A := y in z".to_string(),
                "fun (A : Type) (x : A) => x".to_string()
            ),
            // Beta via type-indexed identity
            TestCase::DefEq(
                "fun (A : Type) (x : A) => (fun (B : Type) (y : B) => y) A x".to_string(),
                "fun (A : Type) (x : A) => x".to_string()
            ),
            // =====================================================================
            // ADDITIONAL NOT DEFEQ TESTS
            // Test more definitional inequality cases
            // =====================================================================
            // Different let bodies
            TestCase::NotDefEq(
                "let x : Type := Prop in x".to_string(),
                "let x : Type := Type in x".to_string()
            ),
            // Same let, different usage
            TestCase::NotDefEq(
                "let x : Type := Prop in Type".to_string(),
                "let x : Type := Prop in x".to_string()
            ),
            // Different lambda bodies
            TestCase::NotDefEq(
                "fun (A : Type) (x : A) (y : A) => x".to_string(),
                "fun (A : Type) (x : A) (y : A) => y".to_string()
            ),
            // Prop-returning vs Type-returning
            TestCase::NotDefEq(
                "fun (P : Prop) (p : P) => p".to_string(),
                "fun (P : Prop) (p : P) => Type".to_string()
            ),
            // Different dependent arrow codomain
            TestCase::NotDefEq(
                "forall (A : Type), A -> A".to_string(),
                "forall (A : Type), A -> Type".to_string()
            ),
            // Different dependent types (using forall syntax)
            TestCase::NotDefEq(
                "forall (A : Type), A".to_string(),
                "forall (A : Type), Type".to_string()
            ),
            // Different function composition order
            TestCase::NotDefEq(
                "fun (A : Type) (B : Type) (f : A -> A) (g : A -> A) (x : A) => f (g x)".to_string(),
                "fun (A : Type) (B : Type) (f : A -> A) (g : A -> A) (x : A) => g (f x)".to_string()
            ),
            // Swap vs identity
            TestCase::NotDefEq(
                "fun (A : Type) (x : A) (y : A) => x".to_string(),
                "fun (A : Type) (x : A) (y : A) => y".to_string()
            ),
            // =====================================================================
            // EDGE CASE TESTS
            // Test boundary conditions and special cases
            // =====================================================================
            // Empty arrow chain
            TestCase::TypeInfer("Type".to_string()),
            // Deeply nested arrows
            TestCase::TypeInfer("Type -> Type -> Type -> Type -> Type".to_string()),
            // Self-referential patterns (valid)
            TestCase::TypeInfer("fun (A : Type) (f : A -> A) => f".to_string()),
            // Multiple identical bindings (shadowing)
            TestCase::TypeInfer("fun (A : Type) (A : A) (A : A) => A".to_string()),
            // Let with same name shadowing
            TestCase::TypeInfer("let A : Type := Type in let A : A := Prop in A".to_string()),
            // Prop -> Type function
            TestCase::TypeInfer("fun (P : Prop) => Type".to_string()),
            // Type -> Prop function
            TestCase::TypeInfer("fun (A : Type) => Prop".to_string()),
            // Higher universe arrows
            TestCase::TypeInfer("(Type -> Type) -> Type".to_string()),
            // Dependent pair-like selector type
            TestCase::TypeInfer("(A : Type) -> (B : A -> Type) -> ((x : A) -> B x -> Type) -> Type".to_string()),
            // =====================================================================
            // ADVANCED CHURCH ENCODING TESTS (N=142)
            // More sophisticated Church numeral operations
            // =====================================================================
            // Church predecessor helper (Kleene predecessor trick)
            // pred = λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u)
            // (type only - the actual predecessor requires more complex encoding)
            TestCase::TypeInfer(
                "fun (n : (A : Type) -> (A -> A) -> A -> A) (A : Type) (f : A -> A) (x : A) => n A f x".to_string()
            ),
            // Church isZero: λn.n (λx.False) True
            // Type: ((A : Type) -> (A -> A) -> A -> A) -> (A : Type) -> A -> A -> A
            TestCase::TypeInfer(
                "fun (n : (A : Type) -> (A -> A) -> A -> A) (A : Type) (t : A) (f : A) => n A (fun (x : A) => f) t".to_string()
            ),
            // Church three
            TestCase::TypeInfer("fun (A : Type) (f : A -> A) (x : A) => f (f (f x))".to_string()),
            // Church four
            TestCase::TypeInfer("fun (A : Type) (f : A -> A) (x : A) => f (f (f (f x)))".to_string()),
            // Church numeral composition (add via fold)
            TestCase::TypeInfer(
                "fun (m : (A : Type) -> (A -> A) -> A -> A) (n : (A : Type) -> (A -> A) -> A -> A) => fun (A : Type) (f : A -> A) (x : A) => m A f (n A f x)".to_string()
            ),
            // =====================================================================
            // ETA EQUIVALENCE TESTS (N=142)
            // In Lean 4, eta is part of definitional equality for functions:
            // f ≡ λx. f x (eta reduction)
            // =====================================================================
            // Eta for functions: f ≡ λx. f x (def eq in Lean 4)
            TestCase::DefEq(
                "fun (A : Type) (B : Type) (f : A -> B) => f".to_string(),
                "fun (A : Type) (B : Type) (f : A -> B) (x : A) => f x".to_string()
            ),
            // Eta in composition: f ≡ λx. f x
            TestCase::DefEq(
                "fun (A : Type) (f : A -> A) => f".to_string(),
                "fun (A : Type) (f : A -> A) (x : A) => f x".to_string()
            ),
            // =====================================================================
            // UNIVERSE POLYMORPHISM PATTERNS (N=142)
            // =====================================================================
            // Polymorphic identity instantiated
            TestCase::TypeInfer(
                "fun (id : (A : Type) -> A -> A) => id Type".to_string()
            ),
            // Polymorphic identity double instantiation
            TestCase::TypeInfer(
                "fun (id : (A : Type) -> A -> A) => id (Type -> Type) (fun (A : Type) => A)".to_string()
            ),
            // Type-level identity applied to arrow type
            TestCase::TypeInfer(
                "fun (F : Type -> Type) => F (Prop -> Prop)".to_string()
            ),
            // =====================================================================
            // COMPLEX LET PATTERNS (N=142)
            // =====================================================================
            // Let with multiple uses
            TestCase::TypeInfer(
                "let id : (A : Type) -> A -> A := fun (A : Type) (x : A) => x in fun (B : Type) (y : B) => id B (id B y)".to_string()
            ),
            // Nested let with dependency
            TestCase::TypeInfer(
                "let F : Type -> Type := fun (A : Type) => A -> A in let G : (A : Type) -> F A := fun (A : Type) (x : A) => x in G".to_string()
            ),
            // Let shadowing with different types
            TestCase::TypeInfer(
                "let x : Type := Type in let x : x := Prop in let x : x := x in x".to_string()
            ),
            // =====================================================================
            // MORE DEFEQ EDGE CASES (N=142)
            // =====================================================================
            // Church zero equals identity on functions
            TestCase::DefEq(
                "fun (A : Type) (f : A -> A) (x : A) => x".to_string(),
                "fun (B : Type) (g : B -> B) (y : B) => y".to_string()
            ),
            // Nested application equivalence
            TestCase::DefEq(
                "fun (A : Type) (f : A -> A) (x : A) => f (f (f x))".to_string(),
                "fun (B : Type) (g : B -> B) (y : B) => g (g (g y))".to_string()
            ),
            // Let that reduces away
            TestCase::DefEq(
                "fun (A : Type) => let unused : Type := Prop in A".to_string(),
                "fun (A : Type) => A".to_string()
            ),
            // Beta through polymorphic type
            TestCase::DefEq(
                "fun (A : Type) (x : A) => (fun (B : Type) (f : B -> B) (y : B) => f y) A (fun (z : A) => z) x".to_string(),
                "fun (A : Type) (x : A) => x".to_string()
            ),
            // Composition associativity (definitional when fully applied)
            TestCase::DefEq(
                "fun (A : Type) (f : A -> A) (g : A -> A) (h : A -> A) (x : A) => f (g (h x))".to_string(),
                "fun (A : Type) (f : A -> A) (g : A -> A) (h : A -> A) (x : A) => f (g (h x))".to_string()
            ),
            // =====================================================================
            // MORE NOT DEFEQ EDGE CASES (N=142)
            // =====================================================================
            // Different number of function applications
            TestCase::NotDefEq(
                "fun (A : Type) (f : A -> A) (x : A) => f x".to_string(),
                "fun (A : Type) (f : A -> A) (x : A) => f (f x)".to_string()
            ),
            // Different Church numerals
            TestCase::NotDefEq(
                "fun (A : Type) (f : A -> A) (x : A) => f (f x)".to_string(), // two
                "fun (A : Type) (f : A -> A) (x : A) => f (f (f x))".to_string() // three
            ),
            // Same structure, different variable use in return
            TestCase::NotDefEq(
                "fun (A : Type) (B : Type) (x : A) (y : B) => x".to_string(),
                "fun (A : Type) (B : Type) (x : A) (y : B) => y".to_string()
            ),
            // Let vs direct (different values)
            TestCase::NotDefEq(
                "fun (A : Type) => let x : Type := A in Prop".to_string(),
                "fun (A : Type) => A".to_string()
            ),
        ]
    }
}

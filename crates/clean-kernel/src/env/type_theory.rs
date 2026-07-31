// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type Theory structures for Environment
//!
//! This module provides axioms and structures for foundational type theory:
//! - Dependent Type Theory (Martin-Löf Type Theory, Calculus of Constructions)
//! - Pure Type Systems (λ-cube, PTS generalizations)
//! - Homotopy Type Theory (HoTT: types as spaces, paths, univalence)
//! - Cubical Type Theory (computational univalence, Kan operations)
//! - Inductive Types (W-types, indexed families, inductives with motives)
//! - Universe Polymorphism (Type : Type issues, universe stratification)
//! - Proof-Relevant vs Proof-Irrelevant types (Prop, SProp, squashing)
//!
//! This is foundational for clean as a proof assistant: the kernel itself
//! is built on dependent type theory with inductives and universes.

#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::Expr;
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    /// Initialize Type Theory module
    ///
    /// Type theory provides the foundational framework for proof assistants:
    /// - Types as propositions (Curry-Howard correspondence)
    /// - Terms as proofs
    /// - Type checking as proof verification
    ///
    /// Key systems:
    /// - MLTT: Martin-Löf Type Theory - the basis for Agda, Coq
    /// - CoC: Calculus of Constructions - impredicative, basis for Coq
    /// - CIC: Calculus of Inductive Constructions - CoC + inductives
    /// - Lean's foundation: CIC variant with quotient types
    /// - HoTT: Types as ∞-groupoids, univalence axiom
    /// - Cubical: Computational interpretation of HoTT
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.type_theory_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`, `bool`, `prod`, `sigma`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_type_theory(&mut self) -> Result<(), EnvError> {
        if self.type_theory_init {
            return Ok(());
        }

        // Dependencies
        // HEq must be initialized before Sigma because Sigma has a dependent
        // field (β a depends on a), and noConfusionType generation uses HEq
        // for dependent fields (Lean 4 NoConfusion.lean:45).
        self.init_eq()?;
        self.init_heq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_prod()?;
        self.init_sigma()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Type Theory constants
        for name in &[
            // ================================================================
            // Judgments and Contexts
            // ================================================================
            "TypeTheory.Context",      // typing context Γ
            "TypeTheory.EmptyCtx",     // empty context ·
            "TypeTheory.CtxExtend",    // context extension Γ, x : A
            "TypeTheory.CtxValid",     // Γ ctx (context well-formed)
            "TypeTheory.Typing",       // Γ ⊢ t : A (typing judgment)
            "TypeTheory.TypeWF",       // Γ ⊢ A type (type well-formed)
            "TypeTheory.DefEq",        // Γ ⊢ t ≡ s : A (definitional eq)
            "TypeTheory.Conv",         // conversion rule
            "TypeTheory.Weakening",    // if Γ ⊢ t : A then Γ, x : B ⊢ t : A
            "TypeTheory.Substitution", // substitution lemma
            // ================================================================
            // Pure Type Systems (PTS)
            // ================================================================
            "TypeTheory.PTS.Sort",       // sorts S (*, □, ...)
            "TypeTheory.PTS.Axiom",      // axiom relation A : S
            "TypeTheory.PTS.Rule",       // rule relation (S₁, S₂, S₃)
            "TypeTheory.PTS.Spec",       // PTS specification (S, A, R)
            "TypeTheory.PTS.Functional", // functional PTS (unique S₃)
            // ================================================================
            // Lambda Cube
            // ================================================================
            "TypeTheory.LambdaCube.STLCTerms", // λ→ : simply typed (terms dep on terms)
            "TypeTheory.LambdaCube.System_F",  // λ2 : polymorphism (terms dep on types)
            "TypeTheory.LambdaCube.System_Fw", // λω : type operators (types dep on types)
            "TypeTheory.LambdaCube.LF",        // λP : dependent types (types dep on terms)
            "TypeTheory.LambdaCube.System_Fw2", // λ2ω : polymorphism + type operators
            "TypeTheory.LambdaCube.CC",        // λPω : Calculus of Constructions (full cube)
            "TypeTheory.LambdaCube.Embedding", // embeddings between systems
            // ================================================================
            // Martin-Löf Type Theory (MLTT)
            // ================================================================
            "TypeTheory.MLTT.Universe",  // U : Type (universe)
            "TypeTheory.MLTT.El",        // El : U → Type (decoding)
            "TypeTheory.MLTT.Pi",        // Π (x : A), B x : dependent product
            "TypeTheory.MLTT.Lambda",    // λ x . e : introduction for Π
            "TypeTheory.MLTT.App",       // f a : elimination for Π
            "TypeTheory.MLTT.Beta",      // (λ x . e) a ≡ e[a/x]
            "TypeTheory.MLTT.Eta",       // f ≡ λ x . f x (η-expansion)
            "TypeTheory.MLTT.Sigma",     // Σ (x : A), B x : dependent sum
            "TypeTheory.MLTT.Pair",      // (a, b) : introduction for Σ
            "TypeTheory.MLTT.Fst",       // π₁ : Σ → first component
            "TypeTheory.MLTT.Snd",       // π₂ : Σ → second component
            "TypeTheory.MLTT.SigmaBeta", // π₁(a,b) ≡ a, π₂(a,b) ≡ b
            "TypeTheory.MLTT.SigmaEta",  // (π₁ p, π₂ p) ≡ p
            // ================================================================
            // Identity Types (Propositional Equality)
            // ================================================================
            "TypeTheory.Id",        // Id A a b : identity type
            "TypeTheory.Refl",      // refl a : Id A a a
            "TypeTheory.J",         // J eliminator (path induction)
            "TypeTheory.JBeta",     // J computation rule
            "TypeTheory.Transport", // transport : Id A a b → P a → P b
            "TypeTheory.Ap",        // ap f : Id A a b → Id B (f a) (f b)
            "TypeTheory.Concat",    // · : Id a b → Id b c → Id a c
            "TypeTheory.Inverse",   // ⁻¹ : Id a b → Id b a
            "TypeTheory.UIP",       // uniqueness of identity proofs
            "TypeTheory.Hedberg",   // decidable eq → UIP
            "TypeTheory.K",         // Streicher's K axiom
            // ================================================================
            // Inductive Types
            // ================================================================
            "TypeTheory.Ind.Spec",             // inductive specification
            "TypeTheory.Ind.Constructor",      // constructor
            "TypeTheory.Ind.Recursor",         // recursor/eliminator
            "TypeTheory.Ind.Motive",           // motive (elimination target)
            "TypeTheory.Ind.Minor",            // minor premises
            "TypeTheory.Ind.ComputationRule",  // computation/ι rule
            "TypeTheory.Ind.Positivity",       // strict positivity condition
            "TypeTheory.Ind.NestedPositive",   // nested positive occurrence
            "TypeTheory.Ind.StrictlyPositive", // no negative occurrences
            // ================================================================
            // W-types (Well-founded Trees)
            // ================================================================
            "TypeTheory.W",            // W (x : A), B x : W-type
            "TypeTheory.W.Sup",        // sup : (a : A) → (B a → W A B) → W A B
            "TypeTheory.W.Rec",        // W-recursor
            "TypeTheory.W.Beta",       // computation rule for W-rec
            "TypeTheory.W.EncodeNat",  // Nat ≅ W Bool (if _ then Empty else Unit)
            "TypeTheory.W.EncodeList", // List A ≅ W (Option A) ...
            // ================================================================
            // Indexed Inductive Types
            // ================================================================
            "TypeTheory.IndIdx.Family", // A : I → Type (indexed family)
            "TypeTheory.IndIdx.Constructor", // constructor with indices
            "TypeTheory.IndIdx.Elim",   // dependent elimination
            "TypeTheory.IndIdx.Vec",    // Vec A n : sized vector
            "TypeTheory.IndIdx.Fin",    // Fin n : finite type
            "TypeTheory.IndIdx.Eq",     // propositional eq as indexed type
            // ================================================================
            // Induction-Recursion
            // ================================================================
            "TypeTheory.IndRec.MutualDef", // mutually define type and function
            "TypeTheory.IndRec.Universe",  // universe closed under operations
            "TypeTheory.IndRec.Code",      // code for type
            "TypeTheory.IndRec.Decode",    // decode code to type
            // ================================================================
            // Induction-Induction
            // ================================================================
            "TypeTheory.IndInd.MutualTypes", // mutually defined types
            "TypeTheory.IndInd.Syntax",      // intrinsically-typed syntax
            // ================================================================
            // Quotient Types
            // ================================================================
            "TypeTheory.Quot",       // Quot A R : quotient type
            "TypeTheory.Quot.Mk",    // Quot.mk : A → Quot A R
            "TypeTheory.Quot.Sound", // R a b → Quot.mk a = Quot.mk b
            "TypeTheory.Quot.Lift",  // lift function respecting equiv
            "TypeTheory.Quot.Ind",   // quotient induction
            "TypeTheory.Quot.Exact", // Quot.mk a = Quot.mk b → R a b
            "TypeTheory.SetQuot",    // set quotient (truncated)
            // ================================================================
            // Universes
            // ================================================================
            "TypeTheory.Univ.Hierarchy",    // Type₀ : Type₁ : Type₂ : ...
            "TypeTheory.Univ.Cumulativity", // A : Type_i → A : Type_{i+1}
            "TypeTheory.Univ.Lift",         // ULift : Type_i → Type_j (j ≥ i)
            "TypeTheory.Univ.Max",          // max u v : level
            "TypeTheory.Univ.Imax",         // imax u v : impredicative max
            "TypeTheory.Univ.Polymorphism", // universe-polymorphic defs
            "TypeTheory.Univ.Girard",       // Type : Type inconsistency
            "TypeTheory.Univ.Hurkens",      // Hurkens paradox
            "TypeTheory.Univ.Russell",      // Russell's paradox in types
            // ================================================================
            // Prop and Proof Irrelevance
            // ================================================================
            "TypeTheory.Prop",               // Prop : Type (propositions)
            "TypeTheory.Prop.Impredicative", // ∀ (P : Prop), _ : Prop
            "TypeTheory.Prop.ProofIrrel",    // proof irrelevance: h₁ = h₂
            "TypeTheory.Prop.Squash",        // ||A|| : Prop (squash/truncation)
            "TypeTheory.Prop.Trunc",         // propositional truncation
            "TypeTheory.Prop.Exists",        // ∃ as truncated Σ
            "TypeTheory.SProp",              // strict Prop (definitional irrel)
            "TypeTheory.Subsingleton",       // at most one inhabitant
            // ================================================================
            // Large Elimination
            // ================================================================
            "TypeTheory.LargeElim",           // elim from Prop to Type
            "TypeTheory.LargeElim.Singleton", // elim from singleton inductives
            "TypeTheory.LargeElim.Empty",     // False → A
            "TypeTheory.LargeElim.Eq",        // eq.rec to Type
            "TypeTheory.LargeElim.Acc",       // Acc.rec to Type (well-founded)
            // ================================================================
            // Calculus of Constructions (CoC)
            // ================================================================
            "TypeTheory.CoC.Term",          // CoC terms
            "TypeTheory.CoC.Star",          // * : □ (Prop type)
            "TypeTheory.CoC.Box",           // □ (type of *)
            "TypeTheory.CoC.Impredicative", // ∀ X : *, ... : *
            "TypeTheory.CoC.Consistency",   // CoC consistent (no closed term of ⊥)
            "TypeTheory.CoC.Normalization", // strong normalization
            // ================================================================
            // Calculus of Inductive Constructions (CIC)
            // ================================================================
            "TypeTheory.CIC.Ind",       // inductive definitions
            "TypeTheory.CIC.Fix",       // fixpoint/recursion
            "TypeTheory.CIC.Guard",     // guardedness condition
            "TypeTheory.CIC.StructRec", // structural recursion
            "TypeTheory.CIC.Match",     // pattern matching
            "TypeTheory.CIC.Case",      // case analysis
            "TypeTheory.CIC.Iota",      // ι-reduction (match on constructor)
            // ================================================================
            // Homotopy Type Theory (HoTT)
            // ================================================================
            "TypeTheory.HoTT.Path",         // Path A a b (identity as path)
            "TypeTheory.HoTT.PathRefl",     // idp : Path A a a
            "TypeTheory.HoTT.PathConcat",   // p · q : path composition
            "TypeTheory.HoTT.PathInverse",  // p⁻¹ : inverse path
            "TypeTheory.HoTT.PathOver",     // PathOver B p u v
            "TypeTheory.HoTT.Apd",          // apd f p : dependent ap
            "TypeTheory.HoTT.Funext",       // function extensionality
            "TypeTheory.HoTT.FunextHApply", // funext and happly inverse
            // ================================================================
            // HoTT: Truncation Levels
            // ================================================================
            "TypeTheory.HoTT.IsContr",    // contractible: unique inhabitant
            "TypeTheory.HoTT.IsProp",     // proposition: at most one
            "TypeTheory.HoTT.IsSet",      // set: UIP holds
            "TypeTheory.HoTT.IsGroupoid", // 1-truncated
            "TypeTheory.HoTT.Is2Groupoid", // 2-truncated
            "TypeTheory.HoTT.TruncLevel", // n-truncation level
            "TypeTheory.HoTT.Trunc",      // n-truncation ||A||ₙ
            "TypeTheory.HoTT.TruncRec",   // eliminator for truncation
            "TypeTheory.HoTT.HTrunc",     // homotopy n-truncation
            // ================================================================
            // HoTT: Univalence
            // ================================================================
            "TypeTheory.HoTT.Equiv",       // A ≃ B : equivalence
            "TypeTheory.HoTT.IsEquiv",     // is-equiv f
            "TypeTheory.HoTT.QInv",        // quasi-inverse
            "TypeTheory.HoTT.BiInv",       // bi-invertible
            "TypeTheory.HoTT.HalfAdjoint", // half-adjoint equivalence
            "TypeTheory.HoTT.IdToEquiv",   // (A = B) → (A ≃ B)
            "TypeTheory.HoTT.Univalence",  // (A ≃ B) ≃ (A = B)
            "TypeTheory.HoTT.UA",          // ua : (A ≃ B) → (A = B)
            "TypeTheory.HoTT.UABeta",      // transport (ua e) = e.1
            "TypeTheory.HoTT.UAEta",       // ua (idToEquiv p) = p
            // ================================================================
            // HoTT: Higher Inductive Types (HITs)
            // ================================================================
            "TypeTheory.HoTT.HIT",            // higher inductive type
            "TypeTheory.HoTT.HIT.PathCtor",   // path constructor
            "TypeTheory.HoTT.HIT.Circle",     // S¹ : circle type
            "TypeTheory.HoTT.HIT.CircleBase", // base : S¹
            "TypeTheory.HoTT.HIT.CircleLoop", // loop : base = base
            "TypeTheory.HoTT.HIT.CircleRec",  // circle eliminator
            "TypeTheory.HoTT.HIT.Interval",   // I : interval type
            "TypeTheory.HoTT.HIT.Susp",       // Σ A : suspension
            "TypeTheory.HoTT.HIT.Pushout",    // pushout
            "TypeTheory.HoTT.HIT.Coeq",       // coequalizer
            "TypeTheory.HoTT.HIT.SetTrunc",   // set truncation ||A||₀
            "TypeTheory.HoTT.HIT.PropTrunc",  // propositional truncation
            // ================================================================
            // HoTT: Homotopy Theory
            // ================================================================
            "TypeTheory.HoTT.LoopSpace",  // Ω A : loop space
            "TypeTheory.HoTT.Pi_n",       // πₙ(A) : n-th homotopy group
            "TypeTheory.HoTT.Fibration",  // fibration
            "TypeTheory.HoTT.Fiber",      // fiber of a map
            "TypeTheory.HoTT.TotalSpace", // total space of fibration
            "TypeTheory.HoTT.PathSpace",  // path space
            "TypeTheory.HoTT.Hopf",       // Hopf fibration
            "TypeTheory.HoTT.Conn",       // n-connected type/map
            "TypeTheory.HoTT.Whitehead",  // Whitehead's theorem
            // ================================================================
            // Cubical Type Theory
            // ================================================================
            "TypeTheory.Cubical.I",         // interval type I
            "TypeTheory.Cubical.I0",        // 0 : I (left endpoint)
            "TypeTheory.Cubical.I1",        // 1 : I (right endpoint)
            "TypeTheory.Cubical.PathP",     // PathP A i0 i1 : path type
            "TypeTheory.Cubical.PathPLam",  // λ i . e : path
            "TypeTheory.Cubical.PathPApp",  // p @ i : path application
            "TypeTheory.Cubical.PathPBeta", // (λ i . e) @ j ≡ e[j/i]
            "TypeTheory.Cubical.PathPEta",  // λ i . p @ i ≡ p
            // ================================================================
            // Cubical: Face Lattice
            // ================================================================
            "TypeTheory.Cubical.Face",     // face formula φ
            "TypeTheory.Cubical.Face1",    // 1F : true face
            "TypeTheory.Cubical.Face0",    // 0F : false face
            "TypeTheory.Cubical.FaceAnd",  // φ ∧ ψ
            "TypeTheory.Cubical.FaceOr",   // φ ∨ ψ
            "TypeTheory.Cubical.FaceI0",   // (i = 0)
            "TypeTheory.Cubical.FaceI1",   // (i = 1)
            "TypeTheory.Cubical.Partial",  // Partial φ A : partial element
            "TypeTheory.Cubical.PartialP", // PartialP φ A : dependent partial
            // ================================================================
            // Cubical: Kan Operations
            // ================================================================
            "TypeTheory.Cubical.Comp",   // comp : composition
            "TypeTheory.Cubical.Hcomp",  // hcomp : homogeneous composition
            "TypeTheory.Cubical.Transp", // transp : transport
            "TypeTheory.Cubical.Fill",   // fill : filler for composition
            "TypeTheory.Cubical.Glue",   // Glue : gluing type
            "TypeTheory.Cubical.Unglue", // unglue operation
            // ================================================================
            // Cubical: Computational Univalence
            // ================================================================
            "TypeTheory.Cubical.GlueType", // Glue [φ ↦ (T, e)] A
            "TypeTheory.Cubical.GlueUA",   // univalence via Glue
            "TypeTheory.Cubical.CompUA",   // ua computes
            "TypeTheory.Cubical.TranspUA", // transport computes on ua
            // ================================================================
            // Cubical: Higher Inductive Types
            // ================================================================
            "TypeTheory.Cubical.HIT",         // cubical HITs
            "TypeTheory.Cubical.HIT.Circle",  // S¹ with path
            "TypeTheory.Cubical.HIT.Torus",   // T² : torus
            "TypeTheory.Cubical.HIT.SetQuot", // set quotient via HIT
            "TypeTheory.Cubical.HIT.Coeq",    // coequalizer
            // ================================================================
            // Setoid Type Theory
            // ================================================================
            "TypeTheory.Setoid",            // setoid: type + equivalence
            "TypeTheory.Setoid.Carrier",    // underlying type
            "TypeTheory.Setoid.Equiv",      // equivalence relation
            "TypeTheory.Setoid.Refl",       // reflexivity
            "TypeTheory.Setoid.Sym",        // symmetry
            "TypeTheory.Setoid.Trans",      // transitivity
            "TypeTheory.Setoid.Morphism",   // setoid morphism
            "TypeTheory.Setoid.Respectful", // respects equivalence
            // ================================================================
            // Observational Type Theory
            // ================================================================
            "TypeTheory.OTT.Obs",       // observational equality
            "TypeTheory.OTT.Coerce",    // coerce along obs eq
            "TypeTheory.OTT.Coherence", // coherence: coerce idempotent
            "TypeTheory.OTT.Coe",       // coe : A ≈ B → A → B
            "TypeTheory.OTT.Coh",       // coh : coe refl = id
            // ================================================================
            // Extensional Type Theory (ETT)
            // ================================================================
            "TypeTheory.ETT.EqRefl",      // equality reflection
            "TypeTheory.ETT.PropEq",      // propositional eq = def eq
            "TypeTheory.ETT.UIP",         // UIP holds
            "TypeTheory.ETT.K",           // K holds
            "TypeTheory.ETT.Undecidable", // type checking undecidable
            // ================================================================
            // Two-Level Type Theory
            // ================================================================
            "TypeTheory.TwoLevel.Inner",   // inner (fibrant) types
            "TypeTheory.TwoLevel.Outer",   // outer (strict) types
            "TypeTheory.TwoLevel.Exo",     // exo-types (strict equality)
            "TypeTheory.TwoLevel.Strict",  // strict equality
            "TypeTheory.TwoLevel.Fibrant", // fibrant types
            // ================================================================
            // Logical Frameworks
            // ================================================================
            "TypeTheory.LF",           // Edinburgh Logical Framework
            "TypeTheory.LF.Kind",      // kinds
            "TypeTheory.LF.Family",    // type families
            "TypeTheory.LF.Object",    // objects
            "TypeTheory.LF.Signature", // signature
            "TypeTheory.LF.Encoding",  // encoding judgments
            "TypeTheory.LF.Adequacy",  // adequacy theorem
            // ================================================================
            // Normalization and Decidability
            // ================================================================
            "TypeTheory.Norm.SN",             // strong normalization
            "TypeTheory.Norm.WN",             // weak normalization
            "TypeTheory.Norm.CR",             // Church-Rosser/confluence
            "TypeTheory.Norm.Decidable",      // decidable type checking
            "TypeTheory.Norm.CanonicalForms", // canonical forms lemma
            "TypeTheory.Norm.NbE",            // normalization by evaluation
            "TypeTheory.Norm.Hereditary",     // hereditary substitution
            // ================================================================
            // Logical Relations
            // ================================================================
            "TypeTheory.LogRel",             // logical relation
            "TypeTheory.LogRel.Unary",       // unary (realizability)
            "TypeTheory.LogRel.Binary",      // binary (parametricity)
            "TypeTheory.LogRel.Step",        // step-indexed
            "TypeTheory.LogRel.Kripke",      // Kripke logical relation
            "TypeTheory.LogRel.Fundamental", // fundamental theorem
            // ================================================================
            // Parametricity
            // ================================================================
            "TypeTheory.Param.Rel",         // relational interpretation
            "TypeTheory.Param.Free",        // free theorems
            "TypeTheory.Param.Abstraction", // abstraction theorem
            "TypeTheory.Param.Identity",    // identity extension
            "TypeTheory.Param.Graph",       // graph lemma
            // ================================================================
            // Realizability
            // ================================================================
            "TypeTheory.Realize.PCA",          // partial combinatory algebra
            "TypeTheory.Realize.KleeneFirst",  // Kleene's first algebra (Nat)
            "TypeTheory.Realize.KleeneSecond", // Kleene's second algebra
            "TypeTheory.Realize.Assembly",     // assemblies
            "TypeTheory.Realize.ModestSet",    // modest sets
            "TypeTheory.Realize.EffTopos",     // effective topos
            // ================================================================
            // Categorical Semantics
            // ================================================================
            "TypeTheory.Cat.CwF",           // category with families
            "TypeTheory.Cat.LCC",           // locally cartesian closed
            "TypeTheory.Cat.Topos",         // topos model
            "TypeTheory.Cat.Presheaf",      // presheaf model
            "TypeTheory.Cat.Cubical",       // cubical sets model
            "TypeTheory.Cat.Simplicial",    // simplicial sets model
            "TypeTheory.Cat.InftyGroupoid", // ∞-groupoid model
            // ================================================================
            // Type-Theoretic Axioms
            // ================================================================
            "TypeTheory.Axiom.LEM",          // law of excluded middle
            "TypeTheory.Axiom.DNE",          // double negation elimination
            "TypeTheory.Axiom.AC",           // axiom of choice
            "TypeTheory.Axiom.Diaconescu",   // AC + Quot → LEM
            "TypeTheory.Axiom.PropExt",      // propositional extensionality
            "TypeTheory.Axiom.FunExt",       // function extensionality
            "TypeTheory.Axiom.QuotSound",    // quotient soundness
            "TypeTheory.Axiom.PropResizing", // propositional resizing
            // ================================================================
            // Set-Theoretic Models
            // ================================================================
            "TypeTheory.Set.Interpretation", // set-theoretic interpretation
            "TypeTheory.Set.TypeAsSet",      // types as sets
            "TypeTheory.Set.Soundness",      // soundness of set model
            "TypeTheory.Set.Completeness",   // completeness
            // ================================================================
            // Impredicativity
            // ================================================================
            "TypeTheory.Impred.Prop",        // impredicative Prop
            "TypeTheory.Impred.System_F",    // impredicative ∀
            "TypeTheory.Impred.CCMathverse", // CC^ω (predicative CoC)
            "TypeTheory.Impred.Paradox",     // impredicativity issues
            // ================================================================
            // Sized Types
            // ================================================================
            "TypeTheory.Sized.Size",      // size (ordinal-like)
            "TypeTheory.Sized.Inf",       // ∞ : Size (limit size)
            "TypeTheory.Sized.Succ",      // size successor
            "TypeTheory.Sized.SizedType", // A @ s : sized type
            "TypeTheory.Sized.Fix",       // sized fixpoint
            "TypeTheory.Sized.Unfold",    // unfold sized recursion
            // ================================================================
            // Guarded Recursion
            // ================================================================
            "TypeTheory.Guarded.Later", // ▷ A : later modality
            "TypeTheory.Guarded.Next",  // next : A → ▷ A
            "TypeTheory.Guarded.Fix",   // guarded fixpoint
            "TypeTheory.Guarded.Loeb",  // Löb induction
            "TypeTheory.Guarded.Clock", // clock quantification
            // ================================================================
            // Program Extraction
            // ================================================================
            "TypeTheory.Extract.Realize",  // extract realizer
            "TypeTheory.Extract.Program",  // extracted program
            "TypeTheory.Extract.Erased",   // erased (computationally irrelevant)
            "TypeTheory.Extract.Relevant", // computationally relevant
        ] {
            let decl = Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            };
            self.add_decl(decl)?;
        }

        self.type_theory_init = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_theory_init() {
        let mut env = Environment::new();
        env.init_type_theory()
            .expect("init_type_theory should succeed");
        assert!(env.type_theory_init);

        // Check key constants exist and have correct names
        for name_str in [
            "TypeTheory.Context",
            "TypeTheory.Typing",
            "TypeTheory.MLTT.Pi",
            "TypeTheory.MLTT.Sigma",
        ] {
            let name = Name::from_string(name_str);
            let info = env
                .get_const(&name)
                .unwrap_or_else(|| panic!("{name_str} should be registered"));
            assert_eq!(info.name, name, "{name_str} constant name mismatch");
        }
    }

    /// Helper: assert constant exists and has matching name in environment.
    fn assert_const_registered(env: &Environment, name_str: &str) {
        let name = Name::from_string(name_str);
        let info = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("{name_str} should be registered"));
        assert_eq!(info.name, name, "{name_str} constant name mismatch");
    }

    #[test]
    fn test_pts_framework() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // Pure Type Systems generalize many type theories
        for name_str in [
            "TypeTheory.PTS.Sort",
            "TypeTheory.PTS.Axiom",
            "TypeTheory.PTS.Rule",
        ] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_lambda_cube() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // The 8 corners of the λ-cube
        for name_str in [
            "TypeTheory.LambdaCube.STLCTerms",
            "TypeTheory.LambdaCube.System_F",
            "TypeTheory.LambdaCube.System_Fw",
            "TypeTheory.LambdaCube.LF",
            "TypeTheory.LambdaCube.CC",
        ] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_mltt_constructs() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // Martin-Löf Type Theory constructs
        for name_str in [
            "TypeTheory.MLTT.Pi",
            "TypeTheory.MLTT.Sigma",
            "TypeTheory.MLTT.Lambda",
            "TypeTheory.MLTT.Beta",
        ] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_identity_types() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // Identity types and their eliminator
        for name_str in [
            "TypeTheory.Id",
            "TypeTheory.Refl",
            "TypeTheory.J",
            "TypeTheory.Transport",
        ] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_inductive_types() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // Inductive type machinery
        for name_str in [
            "TypeTheory.Ind.Spec",
            "TypeTheory.Ind.Recursor",
            "TypeTheory.Ind.Positivity",
        ] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_w_types() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // W-types: well-founded trees
        for name_str in ["TypeTheory.W", "TypeTheory.W.Sup", "TypeTheory.W.Rec"] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_quotient_types() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // Quotient types (key to Lean's foundation)
        for name_str in [
            "TypeTheory.Quot",
            "TypeTheory.Quot.Mk",
            "TypeTheory.Quot.Sound",
            "TypeTheory.Quot.Lift",
        ] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_universes() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // Universe hierarchy and polymorphism
        for name_str in [
            "TypeTheory.Univ.Hierarchy",
            "TypeTheory.Univ.Cumulativity",
            "TypeTheory.Univ.Polymorphism",
            "TypeTheory.Univ.Girard",
        ] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_prop_and_proof_irrelevance() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // Prop and proof-irrelevance
        for name_str in [
            "TypeTheory.Prop",
            "TypeTheory.Prop.Impredicative",
            "TypeTheory.Prop.ProofIrrel",
        ] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_hott_basics() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        // HoTT: paths as identity
        for name_str in [
            "TypeTheory.HoTT.Path",
            "TypeTheory.HoTT.PathConcat",
            "TypeTheory.HoTT.Funext",
        ] {
            assert_const_registered(&env, name_str);
        }
    }

    #[test]
    fn test_hott_truncation() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.HoTT.IsContr");
        assert_const_registered(&env, "TypeTheory.HoTT.IsProp");
        assert_const_registered(&env, "TypeTheory.HoTT.IsSet");
        assert_const_registered(&env, "TypeTheory.HoTT.TruncLevel");
    }

    #[test]
    fn test_hott_univalence() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.HoTT.Equiv");
        assert_const_registered(&env, "TypeTheory.HoTT.IdToEquiv");
        assert_const_registered(&env, "TypeTheory.HoTT.Univalence");
        assert_const_registered(&env, "TypeTheory.HoTT.UA");
    }

    #[test]
    fn test_hott_hits() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.HoTT.HIT");
        assert_const_registered(&env, "TypeTheory.HoTT.HIT.Circle");
        assert_const_registered(&env, "TypeTheory.HoTT.HIT.Susp");
        assert_const_registered(&env, "TypeTheory.HoTT.HIT.Pushout");
    }

    #[test]
    fn test_cubical_type_theory() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.Cubical.I");
        assert_const_registered(&env, "TypeTheory.Cubical.PathP");
        assert_const_registered(&env, "TypeTheory.Cubical.Comp");
        assert_const_registered(&env, "TypeTheory.Cubical.Glue");
    }

    #[test]
    fn test_cubical_faces() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.Cubical.Face");
        assert_const_registered(&env, "TypeTheory.Cubical.Partial");
        assert_const_registered(&env, "TypeTheory.Cubical.PartialP");
    }

    #[test]
    fn test_cubical_kan() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.Cubical.Hcomp");
        assert_const_registered(&env, "TypeTheory.Cubical.Transp");
        assert_const_registered(&env, "TypeTheory.Cubical.Fill");
    }

    #[test]
    fn test_categorical_semantics() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.Cat.CwF");
        assert_const_registered(&env, "TypeTheory.Cat.LCC");
        assert_const_registered(&env, "TypeTheory.Cat.Topos");
    }

    #[test]
    fn test_normalization() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.Norm.SN");
        assert_const_registered(&env, "TypeTheory.Norm.CR");
        assert_const_registered(&env, "TypeTheory.Norm.Decidable");
    }

    #[test]
    fn test_logical_relations() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.LogRel");
        assert_const_registered(&env, "TypeTheory.LogRel.Fundamental");
    }

    #[test]
    fn test_axioms() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.Axiom.LEM");
        assert_const_registered(&env, "TypeTheory.Axiom.AC");
        assert_const_registered(&env, "TypeTheory.Axiom.FunExt");
        assert_const_registered(&env, "TypeTheory.Axiom.PropExt");
    }

    #[test]
    fn test_sized_types() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.Sized.Size");
        assert_const_registered(&env, "TypeTheory.Sized.Fix");
    }

    #[test]
    fn test_guarded_recursion() {
        let mut env = Environment::new();
        env.init_type_theory().unwrap();

        assert_const_registered(&env, "TypeTheory.Guarded.Later");
        assert_const_registered(&env, "TypeTheory.Guarded.Fix");
        assert_const_registered(&env, "TypeTheory.Guarded.Loeb");
    }

    #[test]
    fn test_type_theory_key_types_well_formed() {
        use crate::expr::ExprKind;
        use crate::level::Level;
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_type_theory().unwrap();
        let tc = TypeChecker::new(&env);

        // Sample constants across HoTT, cubical, axioms, and guarded recursion
        for name in &[
            "TypeTheory.HoTT.Univalence",
            "TypeTheory.Cubical.PathP",
            "TypeTheory.Axiom.FunExt",
            "TypeTheory.Guarded.Later",
            "TypeTheory.Norm.SN",
            "TypeTheory.Cat.Topos",
        ] {
            let expr = Expr::const_(Name::from_string(name), vec![Level::zero()]);
            let ty = tc
                .infer_type(&expr)
                .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
            assert!(
                matches!(&ty.kind, ExprKind::Sort(_)),
                "{name}: expected Sort type, got {ty:?}"
            );
        }

        // Verify universe level params on a sample
        let ua_info = env
            .get_const(&Name::from_string("TypeTheory.HoTT.UA"))
            .expect("TypeTheory.HoTT.UA");
        assert!(
            !ua_info.level_params.is_empty(),
            "TypeTheory.HoTT.UA should have universe parameters"
        );
    }
}

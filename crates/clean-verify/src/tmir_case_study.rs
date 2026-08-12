// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! tMIR integration case study: end-to-end verification of a Rust function
//! through the clean kernel.
//!
//! This module demonstrates the full pipeline:
//!   Rust source -> tMIR IR -> clean declarations -> kernel type-checking
//!
//! # Case Study: `fn abs(x: i32) -> i32`
//!
//! The specification states:
//!   forall x : Int, abs(x) >= 0 /\ (abs(x) = x \/ abs(x) = Int.neg x)
//!
//! The pipeline stages are:
//! 1. **Type registration**: Map Rust types (i32) to kernel types (Int)
//! 2. **Operation axioms**: Register domain axioms for i32 operations
//!    (nonneg predicate, abs semantics via Int.rec)
//! 3. **Function definition**: Define `abs_i32` as a kernel Definition
//! 4. **Specification statement**: State the postcondition as a Prop
//! 5. **Proof construction**: Build a proof term discharging the spec
//! 6. **Kernel verification**: `add_decl` type-checks everything
//!
//! # Architecture Notes
//!
//! This uses the clean kernel's public API directly (`Environment`, `Expr`,
//! `Declaration`, `Name`, `Level`), exactly as a tMIR backend would. No
//! internal builder helpers are used -- all de Bruijn indices are computed
//! explicitly, modeling what an IR compiler would produce.

#[cfg(test)]
mod tests {
    use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};

    // =====================================================================
    // Helper: universe level 1 (Type)
    // =====================================================================
    fn level_one() -> Level {
        Level::succ(Level::zero())
    }

    // =====================================================================
    // Helper: common constant references
    // =====================================================================
    fn int_const() -> Expr {
        Expr::const_str("Int")
    }

    fn int_of_nat() -> Expr {
        Expr::const_str("Int.ofNat")
    }

    fn int_neg_succ() -> Expr {
        Expr::const_str("Int.negSucc")
    }

    fn nat_const() -> Expr {
        Expr::const_str("Nat")
    }

    fn nat_zero() -> Expr {
        Expr::const_str("Nat.zero")
    }

    fn nat_succ() -> Expr {
        Expr::const_str("Nat.succ")
    }

    /// Construct `Int.ofNat Nat.zero` (i.e., 0 as Int).
    fn int_zero() -> Expr {
        Expr::app(int_of_nat(), nat_zero())
    }

    /// Construct `Int.ofNat (Nat.succ ... Nat.zero)` for small positive n.
    fn int_pos(n: u32) -> Expr {
        let mut nat = nat_zero();
        for _ in 0..n {
            nat = Expr::app(nat_succ(), nat);
        }
        Expr::app(int_of_nat(), nat)
    }

    /// `@Eq.{1} Int a b`
    fn eq_int(a: Expr, b: Expr) -> Expr {
        let eq = Expr::const_str_levels("Eq", vec![level_one()]);
        Expr::apps(eq, [int_const(), a, b])
    }

    /// `@Eq.refl.{1} Int a`
    fn eq_refl_int(a: Expr) -> Expr {
        let refl = Expr::const_str_levels("Eq.refl", vec![level_one()]);
        Expr::apps(refl, [int_const(), a])
    }

    /// `@And P Q`
    fn and_prop(a: Expr, b: Expr) -> Expr {
        let and = Expr::const_str("And");
        Expr::apps(and, [a, b])
    }

    /// `@And.intro P Q hp hq`
    fn and_intro(p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        let intro = Expr::const_str("And.intro");
        Expr::apps(intro, [p, q, hp, hq])
    }

    /// `@Or P Q`
    fn or_prop(a: Expr, b: Expr) -> Expr {
        let or = Expr::const_str("Or");
        Expr::apps(or, [a, b])
    }

    /// `@Or.inl P Q hp`
    fn or_inl(p: Expr, q: Expr, hp: Expr) -> Expr {
        let inl = Expr::const_str("Or.inl");
        Expr::apps(inl, [p, q, hp])
    }

    /// `@Or.inr P Q hq`
    fn or_inr(p: Expr, q: Expr, hq: Expr) -> Expr {
        let inr = Expr::const_str("Or.inr");
        Expr::apps(inr, [p, q, hq])
    }

    // =====================================================================
    // Stage 1: Environment setup with Int type
    // =====================================================================

    /// Create a prelude environment with Or initialized (needed for spec).
    fn setup_env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_or().expect("Or initialization should succeed");
        env
    }

    // =====================================================================
    // Stage 2: Define abs_i32 as a kernel Definition
    // =====================================================================

    /// Register the `tmir.abs_i32` function definition.
    ///
    /// Lean 4 equivalent:
    ///   def tmir.abs_i32 : Int -> Int :=
    ///     fun x => Int.rec
    ///       (fun n => Int.ofNat n)       -- ofNat case: |n| = n
    ///       (fun n => Int.ofNat (n + 1)) -- negSucc case: |-(n+1)| = n+1
    ///       x
    ///
    /// This uses `Int.rec` (the recursor) for pattern matching, exactly as
    /// tMIR would compile a `match` expression on an inductive type.
    fn register_abs_i32(env: &mut Environment) -> Result<(), clean_kernel::EnvError> {
        let int = int_const();
        let nat = nat_const();

        // Int.rec.{1} : (motive : Int -> Sort 1) -> ... -> Int -> motive x
        let int_rec = Expr::const_str_levels("Int.rec", vec![level_one()]);

        // motive : fun (_ : Int) => Int
        let motive = Expr::lam(BinderInfo::Default, int.clone(), int.clone());

        // ofNat case: fun (n : Nat) => Int.ofNat n
        // Body uses BVar(0) to reference the bound variable n
        let of_nat_case = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(int_of_nat(), Expr::bvar(0)),
        );

        // negSucc case: fun (n : Nat) => Int.ofNat (Nat.succ n)
        // |-(n+1)| = n+1 = Nat.succ n, wrapped in Int.ofNat
        let neg_succ_case = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(int_of_nat(), Expr::app(nat_succ(), Expr::bvar(0))),
        );

        // Full body: fun (x : Int) => Int.rec motive of_nat_case neg_succ_case x
        let body = Expr::lam(
            BinderInfo::Default,
            int.clone(),
            Expr::apps(
                int_rec,
                [
                    motive,
                    of_nat_case,
                    neg_succ_case,
                    Expr::bvar(0), // x
                ],
            ),
        );

        // type: Int -> Int
        let ty = Expr::arrow(int.clone(), int);

        env.add_decl(Declaration::Definition {
            name: Name::from_string("tmir.abs_i32"),
            level_params: vec![],
            type_: ty,
            value: body,
            is_reducible: true,
        })
    }

    // =====================================================================
    // Stage 3: Register nonneg predicate as an axiom
    // =====================================================================

    /// Register `tmir.Int.nonneg : Int -> Prop` as an axiom.
    ///
    /// This models the concept "x >= 0" for integers. In a full tMIR
    /// integration, this would be derived from the integer ordering, but
    /// for the case study we axiomatize it with specific instances.
    fn register_nonneg_axiom(env: &mut Environment) -> Result<(), clean_kernel::EnvError> {
        let int = int_const();
        let prop = Expr::prop();

        // tmir.Int.nonneg : Int -> Prop
        let nonneg_type = Expr::arrow(int, prop);

        env.add_decl(Declaration::Axiom {
            name: Name::from_string("tmir.Int.nonneg"),
            level_params: vec![],
            type_: nonneg_type,
        })
    }

    /// Register `tmir.Int.nonneg_ofNat : forall (n : Nat), tmir.Int.nonneg (Int.ofNat n)`
    ///
    /// Axiom: all natural numbers embedded in Int are non-negative.
    fn register_nonneg_ofnat_axiom(env: &mut Environment) -> Result<(), clean_kernel::EnvError> {
        let nat = nat_const();
        let nonneg = Expr::const_str("tmir.Int.nonneg");

        // forall (n : Nat), tmir.Int.nonneg (Int.ofNat n)
        // Pi (n : Nat) . nonneg (ofNat (BVar 0))
        let ty = Expr::pi(
            BinderInfo::Default,
            nat,
            Expr::app(nonneg, Expr::app(int_of_nat(), Expr::bvar(0))),
        );

        env.add_decl(Declaration::Axiom {
            name: Name::from_string("tmir.Int.nonneg_ofNat"),
            level_params: vec![],
            type_: ty,
        })
    }

    // =====================================================================
    // Stage 4: State the specification
    // =====================================================================

    /// Build the specification type for `abs_i32` applied to `Int.ofNat n`:
    ///
    ///   abs_i32 (Int.ofNat n) = Int.ofNat n
    ///
    /// This is the positive/zero branch of the spec, provable by reflexivity
    /// after reduction.
    fn spec_abs_ofnat_eq(n_bvar: Expr) -> Expr {
        let abs_fn = Expr::const_str("tmir.abs_i32");
        let arg = Expr::app(int_of_nat(), n_bvar.clone());
        let lhs = Expr::app(abs_fn, arg.clone());
        eq_int(lhs, arg)
    }

    /// Build the specification type for `abs_i32` applied to `Int.negSucc n`:
    ///
    ///   abs_i32 (Int.negSucc n) = Int.ofNat (Nat.succ n)
    ///
    /// This is the negative branch, provable by reflexivity after reduction.
    fn spec_abs_negsucc_eq(n_bvar: Expr) -> Expr {
        let abs_fn = Expr::const_str("tmir.abs_i32");
        let arg = Expr::app(int_neg_succ(), n_bvar.clone());
        let lhs = Expr::app(abs_fn, arg);
        let rhs = Expr::app(int_of_nat(), Expr::app(nat_succ(), n_bvar));
        eq_int(lhs, rhs)
    }

    // =====================================================================
    // Test 1: Environment has Int type with constructors
    // =====================================================================

    #[test]
    fn test_tmir_stage1_int_type_available() {
        let env = setup_env();

        // Verify Int inductive type is registered
        let int_name = Name::from_string("Int");
        let int_ind = env
            .get_inductive(&int_name)
            .expect("Int inductive should be in prelude");
        assert_eq!(int_ind.name, int_name);
        assert_eq!(
            int_ind.constructor_names.len(),
            2,
            "Int should have 2 constructors: ofNat and negSucc"
        );

        // Verify constructors are registered
        let ofnat_name = Name::from_string("Int.ofNat");
        let ci = env
            .get_const(&ofnat_name)
            .expect("Int.ofNat should be registered");
        assert_eq!(ci.name, ofnat_name);

        let negsucc_name = Name::from_string("Int.negSucc");
        let ci = env
            .get_const(&negsucc_name)
            .expect("Int.negSucc should be registered");
        assert_eq!(ci.name, negsucc_name);

        // Verify Or is available for the spec
        let or_name = Name::from_string("Or");
        env.get_inductive(&or_name)
            .expect("Or should be available after init_or");
    }

    // =====================================================================
    // Test 2: abs_i32 definition type-checks through the kernel
    // =====================================================================

    #[test]
    fn test_tmir_stage2_abs_definition_typechecks() {
        let mut env = setup_env();

        register_abs_i32(&mut env).expect("abs_i32 definition should pass kernel type-checking");

        // Verify the definition was registered
        let abs_name = Name::from_string("tmir.abs_i32");
        let ci = env
            .get_const(&abs_name)
            .expect("tmir.abs_i32 should be registered");
        assert_eq!(ci.name, abs_name);

        // Verify it has a value (it's a Definition, not an Axiom)
        assert!(
            ci.value.is_some(),
            "tmir.abs_i32 should be a definition with a value"
        );

        // Verify the type is Int -> Int
        let ty = &ci.type_;
        assert!(
            ty.is_pi(),
            "tmir.abs_i32 type should be a Pi/arrow type (Int -> Int)"
        );
    }

    // =====================================================================
    // Test 3: Domain axioms register correctly
    // =====================================================================

    #[test]
    fn test_tmir_stage3_domain_axioms() {
        let mut env = setup_env();

        register_nonneg_axiom(&mut env).expect("nonneg axiom should register");

        register_nonneg_ofnat_axiom(&mut env).expect("nonneg_ofNat axiom should register");

        // Verify both are registered as axioms (no value)
        let nonneg_name = Name::from_string("tmir.Int.nonneg");
        let ci = env.get_const(&nonneg_name).expect("nonneg should exist");
        assert!(ci.value.is_none(), "nonneg should be an axiom");

        let nonneg_ofnat_name = Name::from_string("tmir.Int.nonneg_ofNat");
        let ci = env
            .get_const(&nonneg_ofnat_name)
            .expect("nonneg_ofNat should exist");
        assert!(ci.value.is_none(), "nonneg_ofNat should be an axiom");
    }

    // =====================================================================
    // Test 4: Prove abs(n) = n for non-negative input (ofNat case)
    // =====================================================================

    #[test]
    fn test_tmir_stage4_abs_ofnat_proof() {
        let mut env = setup_env();
        register_abs_i32(&mut env).expect("abs_i32 should register");

        // Theorem: forall (n : Nat), abs_i32 (Int.ofNat n) = Int.ofNat n
        //
        // Proof: fun (n : Nat) => Eq.refl (Int.ofNat n)
        //
        // This works because abs_i32 is reducible and the kernel unfolds:
        //   abs_i32 (Int.ofNat n)
        //   = Int.rec motive ofNat_case negSucc_case (Int.ofNat n)
        //   = ofNat_case n
        //   = Int.ofNat n
        // So `abs_i32 (Int.ofNat n)` is definitionally equal to `Int.ofNat n`.

        let nat = nat_const();

        // Type: forall (n : Nat), abs_i32 (Int.ofNat n) = Int.ofNat n
        let theorem_type = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            spec_abs_ofnat_eq(Expr::bvar(0)),
        );

        // Proof: fun (n : Nat) => @Eq.refl.{1} Int (Int.ofNat n)
        let proof = Expr::lam(
            BinderInfo::Default,
            nat,
            eq_refl_int(Expr::app(int_of_nat(), Expr::bvar(0))),
        );

        env.add_decl(Declaration::Theorem {
            name: Name::from_string("tmir.abs_ofNat_eq"),
            level_params: vec![],
            type_: theorem_type,
            value: proof,
        })
        .expect("abs_ofNat_eq theorem should be kernel-verified");

        // Verify the theorem was registered
        let thm_name = Name::from_string("tmir.abs_ofNat_eq");
        let ci = env.get_const(&thm_name).expect("theorem should exist");
        assert_eq!(ci.name, thm_name);
    }

    // =====================================================================
    // Test 5: Prove abs(-(n+1)) = n+1 for negative input (negSucc case)
    // =====================================================================

    #[test]
    fn test_tmir_stage5_abs_negsucc_proof() {
        let mut env = setup_env();
        register_abs_i32(&mut env).expect("abs_i32 should register");

        // Theorem: forall (n : Nat), abs_i32 (Int.negSucc n) = Int.ofNat (Nat.succ n)
        //
        // Proof: fun (n : Nat) => Eq.refl (Int.ofNat (Nat.succ n))
        //
        // Kernel unfolds:
        //   abs_i32 (Int.negSucc n)
        //   = Int.rec motive ofNat_case negSucc_case (Int.negSucc n)
        //   = negSucc_case n
        //   = Int.ofNat (Nat.succ n)

        let nat = nat_const();

        // Type: forall (n : Nat), abs_i32 (Int.negSucc n) = Int.ofNat (Nat.succ n)
        let theorem_type = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            spec_abs_negsucc_eq(Expr::bvar(0)),
        );

        // Proof: fun (n : Nat) => @Eq.refl.{1} Int (Int.ofNat (Nat.succ n))
        let proof = Expr::lam(
            BinderInfo::Default,
            nat,
            eq_refl_int(Expr::app(
                int_of_nat(),
                Expr::app(nat_succ(), Expr::bvar(0)),
            )),
        );

        env.add_decl(Declaration::Theorem {
            name: Name::from_string("tmir.abs_negSucc_eq"),
            level_params: vec![],
            type_: theorem_type,
            value: proof,
        })
        .expect("abs_negSucc_eq theorem should be kernel-verified");

        let thm_name = Name::from_string("tmir.abs_negSucc_eq");
        let ci = env.get_const(&thm_name).expect("theorem should exist");
        assert_eq!(ci.name, thm_name);
    }

    // =====================================================================
    // Test 6: Prove abs is non-negative (uses domain axiom)
    // =====================================================================

    #[test]
    fn test_tmir_stage6_abs_nonneg() {
        let mut env = setup_env();
        register_abs_i32(&mut env).expect("abs_i32 should register");
        register_nonneg_axiom(&mut env).expect("nonneg should register");
        register_nonneg_ofnat_axiom(&mut env).expect("nonneg_ofNat should register");

        // Theorem: forall (n : Nat), tmir.Int.nonneg (abs_i32 (Int.ofNat n))
        //
        // Proof: fun (n : Nat) => tmir.Int.nonneg_ofNat n
        //
        // Since abs_i32 (Int.ofNat n) reduces to Int.ofNat n, and we have
        // nonneg_ofNat : forall n, nonneg (Int.ofNat n), the proof is direct.

        let nat = nat_const();
        let abs_fn = Expr::const_str("tmir.abs_i32");
        let nonneg = Expr::const_str("tmir.Int.nonneg");
        let nonneg_ofnat = Expr::const_str("tmir.Int.nonneg_ofNat");

        // Type: forall (n : Nat), tmir.Int.nonneg (tmir.abs_i32 (Int.ofNat n))
        let theorem_type = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(
                nonneg,
                Expr::app(abs_fn, Expr::app(int_of_nat(), Expr::bvar(0))),
            ),
        );

        // Proof: fun (n : Nat) => tmir.Int.nonneg_ofNat n
        // This works because abs_i32 (Int.ofNat n) reduces to Int.ofNat n,
        // so the kernel sees: nonneg (Int.ofNat n) which matches nonneg_ofNat n.
        let proof = Expr::lam(
            BinderInfo::Default,
            nat,
            Expr::app(nonneg_ofnat, Expr::bvar(0)),
        );

        env.add_decl(Declaration::Theorem {
            name: Name::from_string("tmir.abs_ofNat_nonneg"),
            level_params: vec![],
            type_: theorem_type,
            value: proof,
        })
        .expect("abs_ofNat_nonneg should be kernel-verified via axiom + reduction");

        let thm_name = Name::from_string("tmir.abs_ofNat_nonneg");
        env.get_const(&thm_name).expect("theorem should exist");
    }

    // =====================================================================
    // Test 7: Full spec -- abs returns original or negation (ofNat case)
    // =====================================================================

    #[test]
    fn test_tmir_stage7_full_spec_ofnat_case() {
        let mut env = setup_env();
        register_abs_i32(&mut env).expect("abs_i32 should register");
        register_nonneg_axiom(&mut env).expect("nonneg should register");
        register_nonneg_ofnat_axiom(&mut env).expect("nonneg_ofNat should register");

        // Full specification for the ofNat case:
        //   forall (n : Nat),
        //     tmir.Int.nonneg (abs_i32 (Int.ofNat n))
        //     /\ (abs_i32 (Int.ofNat n) = Int.ofNat n
        //         \/ abs_i32 (Int.ofNat n) = Int.neg (Int.ofNat n))
        //
        // For the ofNat case, we prove the left disjunct (abs = x) via Or.inl.

        let nat = nat_const();
        let abs_fn = Expr::const_str("tmir.abs_i32");
        let nonneg = Expr::const_str("tmir.Int.nonneg");
        let nonneg_ofnat = Expr::const_str("tmir.Int.nonneg_ofNat");
        let int_neg = Expr::const_str("Int.neg");

        // Build the spec components with BVar(0) = n
        let n = Expr::bvar(0);
        let ofnat_n = Expr::app(int_of_nat(), n.clone());
        let abs_ofnat_n = Expr::app(abs_fn.clone(), ofnat_n.clone());

        // Part 1: nonneg (abs_i32 (Int.ofNat n))
        let nonneg_part = Expr::app(nonneg, abs_ofnat_n.clone());

        // Part 2a: abs_i32 (Int.ofNat n) = Int.ofNat n
        let eq_original = eq_int(abs_ofnat_n.clone(), ofnat_n.clone());

        // Part 2b: abs_i32 (Int.ofNat n) = Int.neg (Int.ofNat n)
        let eq_negated = eq_int(abs_ofnat_n, Expr::app(int_neg, ofnat_n.clone()));

        // Part 2: eq_original \/ eq_negated
        let disjunction = or_prop(eq_original.clone(), eq_negated.clone());

        // Full spec: nonneg_part /\ disjunction
        let full_spec = and_prop(nonneg_part.clone(), disjunction.clone());

        let theorem_type = Expr::pi(BinderInfo::Default, nat.clone(), full_spec);

        // Proof construction:
        //   fun (n : Nat) => And.intro
        //     (nonneg_part)
        //     (disjunction)
        //     (nonneg_ofNat n)                    -- proof of nonneg part
        //     (Or.inl eq_original eq_negated      -- choose left disjunct
        //       (Eq.refl (Int.ofNat n)))           -- proof of equality
        let proof = Expr::lam(BinderInfo::Default, nat, {
            // Inside the lambda, BVar(0) = n
            let n = Expr::bvar(0);
            let ofnat_n = Expr::app(int_of_nat(), n.clone());

            // Proof of nonneg part
            let h_nonneg = Expr::app(nonneg_ofnat, n);

            // Proof of equality: Eq.refl (Int.ofNat n)
            let h_eq = eq_refl_int(ofnat_n);

            // Proof of disjunction: Or.inl eq_original eq_negated h_eq
            let h_disj = or_inl(eq_original.clone(), eq_negated.clone(), h_eq);

            // And.intro nonneg_part disjunction h_nonneg h_disj
            and_intro(nonneg_part, disjunction, h_nonneg, h_disj)
        });

        env.add_decl(Declaration::Theorem {
            name: Name::from_string("tmir.abs_i32_spec_ofNat"),
            level_params: vec![],
            type_: theorem_type,
            value: proof,
        })
        .expect("full abs_i32 spec for ofNat case should be kernel-verified");

        let thm_name = Name::from_string("tmir.abs_i32_spec_ofNat");
        let ci = env.get_const(&thm_name).expect("spec theorem should exist");
        assert_eq!(ci.name, thm_name);
        // Verify it's a theorem (has a proof value), not just an axiom
        assert!(
            ci.value.is_some(),
            "spec theorem should have a proof value (not an axiom)"
        );
    }

    // =====================================================================
    // Test 8: Full spec -- negSucc case (abs returns negation)
    // =====================================================================

    #[test]
    fn test_tmir_stage8_full_spec_negsucc_case() {
        let mut env = setup_env();
        register_abs_i32(&mut env).expect("abs_i32 should register");
        register_nonneg_axiom(&mut env).expect("nonneg should register");
        register_nonneg_ofnat_axiom(&mut env).expect("nonneg_ofNat should register");

        // For the negSucc case:
        //   forall (n : Nat),
        //     tmir.Int.nonneg (abs_i32 (Int.negSucc n))
        //     /\ (abs_i32 (Int.negSucc n) = Int.negSucc n
        //         \/ abs_i32 (Int.negSucc n) = Int.neg (Int.negSucc n))
        //
        // abs_i32 (Int.negSucc n) reduces to Int.ofNat (Nat.succ n).
        // We prove the right disjunct: abs_i32 (Int.negSucc n) = Int.neg (Int.negSucc n)
        //
        // However, Int.neg (Int.negSucc n) = Int.ofNat (Nat.succ n) by definition.
        // So both sides reduce to Int.ofNat (Nat.succ n), and Eq.refl suffices.

        let nat = nat_const();
        let abs_fn = Expr::const_str("tmir.abs_i32");
        let nonneg = Expr::const_str("tmir.Int.nonneg");
        let nonneg_ofnat = Expr::const_str("tmir.Int.nonneg_ofNat");
        let int_neg = Expr::const_str("Int.neg");

        let n = Expr::bvar(0);
        let negsucc_n = Expr::app(int_neg_succ(), n.clone());
        let abs_negsucc_n = Expr::app(abs_fn.clone(), negsucc_n.clone());

        // nonneg (abs_i32 (Int.negSucc n))
        // abs reduces to Int.ofNat (Nat.succ n), so this needs nonneg_ofNat (Nat.succ n)
        let nonneg_part = Expr::app(nonneg, abs_negsucc_n.clone());

        // abs_i32 (Int.negSucc n) = Int.negSucc n  (left disjunct, false for this case)
        let eq_original = eq_int(abs_negsucc_n.clone(), negsucc_n.clone());

        // abs_i32 (Int.negSucc n) = Int.neg (Int.negSucc n)  (right disjunct, true)
        let eq_negated = eq_int(abs_negsucc_n, Expr::app(int_neg.clone(), negsucc_n));

        let disjunction = or_prop(eq_original.clone(), eq_negated.clone());
        let full_spec = and_prop(nonneg_part.clone(), disjunction.clone());

        let theorem_type = Expr::pi(BinderInfo::Default, nat.clone(), full_spec);

        // Proof:
        //   fun (n : Nat) => And.intro _ _
        //     (nonneg_ofNat (Nat.succ n))
        //     (Or.inr _ _ (Eq.refl (Int.ofNat (Nat.succ n))))
        //
        // Both abs_i32 (Int.negSucc n) and Int.neg (Int.negSucc n) reduce to
        // Int.ofNat (Nat.succ n), so Eq.refl works for the right disjunct.
        let proof = Expr::lam(BinderInfo::Default, nat, {
            let n = Expr::bvar(0);
            let succ_n = Expr::app(nat_succ(), n.clone());
            let ofnat_succ_n = Expr::app(int_of_nat(), succ_n.clone());

            // nonneg proof: nonneg_ofNat (Nat.succ n)
            let h_nonneg = Expr::app(nonneg_ofnat, succ_n);

            // equality proof: Eq.refl (Int.ofNat (Nat.succ n))
            let h_eq = eq_refl_int(ofnat_succ_n);

            // disjunction: Or.inr _ _ h_eq
            let h_disj = or_inr(eq_original.clone(), eq_negated.clone(), h_eq);

            and_intro(nonneg_part, disjunction, h_nonneg, h_disj)
        });

        env.add_decl(Declaration::Theorem {
            name: Name::from_string("tmir.abs_i32_spec_negSucc"),
            level_params: vec![],
            type_: theorem_type,
            value: proof,
        })
        .expect("full abs_i32 spec for negSucc case should be kernel-verified");

        let thm_name = Name::from_string("tmir.abs_i32_spec_negSucc");
        let ci = env.get_const(&thm_name).expect("spec theorem should exist");
        assert!(ci.value.is_some(), "should have a proof value");
    }

    // =====================================================================
    // Test 9: Concrete verification -- abs(0) = 0
    // =====================================================================

    #[test]
    fn test_tmir_stage9_concrete_abs_zero() {
        let mut env = setup_env();
        register_abs_i32(&mut env).expect("abs_i32 should register");

        // Theorem: abs_i32 (Int.ofNat Nat.zero) = Int.ofNat Nat.zero
        // i.e., abs(0) = 0
        //
        // Proof: Eq.refl (Int.ofNat Nat.zero)
        let abs_fn = Expr::const_str("tmir.abs_i32");
        let zero = int_zero();
        let abs_zero = Expr::app(abs_fn, zero.clone());

        let ty = eq_int(abs_zero, zero.clone());
        let proof = eq_refl_int(zero);

        env.add_decl(Declaration::Theorem {
            name: Name::from_string("tmir.abs_zero_eq_zero"),
            level_params: vec![],
            type_: ty,
            value: proof,
        })
        .expect("abs(0) = 0 should be kernel-verified by reduction");

        env.get_const(&Name::from_string("tmir.abs_zero_eq_zero"))
            .expect("theorem should be registered");
    }

    // =====================================================================
    // Test 10: Concrete verification -- abs(-1) = 1
    // =====================================================================

    #[test]
    fn test_tmir_stage10_concrete_abs_neg_one() {
        let mut env = setup_env();
        register_abs_i32(&mut env).expect("abs_i32 should register");

        // Theorem: abs_i32 (Int.negSucc Nat.zero) = Int.ofNat (Nat.succ Nat.zero)
        // i.e., abs(-1) = 1
        //
        // Int.negSucc Nat.zero represents -(0+1) = -1
        // abs_i32 (Int.negSucc 0) reduces to Int.ofNat (Nat.succ 0) = 1
        let abs_fn = Expr::const_str("tmir.abs_i32");
        let neg_one = Expr::app(int_neg_succ(), nat_zero());
        let abs_neg_one = Expr::app(abs_fn, neg_one);
        let one = int_pos(1);

        let ty = eq_int(abs_neg_one, one.clone());
        let proof = eq_refl_int(one);

        env.add_decl(Declaration::Theorem {
            name: Name::from_string("tmir.abs_neg_one_eq_one"),
            level_params: vec![],
            type_: ty,
            value: proof,
        })
        .expect("abs(-1) = 1 should be kernel-verified by reduction");

        env.get_const(&Name::from_string("tmir.abs_neg_one_eq_one"))
            .expect("theorem should be registered");
    }

    // =====================================================================
    // Test 11: Negative test -- wrong proof is rejected
    // =====================================================================

    #[test]
    fn test_tmir_stage11_wrong_proof_rejected() {
        let mut env = setup_env();
        register_abs_i32(&mut env).expect("abs_i32 should register");

        // Try to "prove" abs(-1) = 0 (which is FALSE)
        // The kernel should reject this.
        let abs_fn = Expr::const_str("tmir.abs_i32");
        let neg_one = Expr::app(int_neg_succ(), nat_zero());
        let abs_neg_one = Expr::app(abs_fn, neg_one);
        let zero = int_zero();

        // Claim: abs(-1) = 0 (false!)
        let ty = eq_int(abs_neg_one, zero.clone());
        // "Proof": Eq.refl 0 (this proves 0 = 0, not abs(-1) = 0)
        let bogus_proof = eq_refl_int(zero);

        let result = env.add_decl(Declaration::Theorem {
            name: Name::from_string("tmir.bogus_abs"),
            level_params: vec![],
            type_: ty,
            value: bogus_proof,
        });

        assert!(
            result.is_err(),
            "kernel should reject incorrect proof: abs(-1) != 0"
        );
    }
}

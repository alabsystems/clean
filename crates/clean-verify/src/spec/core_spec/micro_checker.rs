// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Micro-checker model, types, operations, and correctness (PARTs 14-17)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_micro_checker(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 14: Micro-Checker Model
        // =========================================================

        // MicroLevel type (universe levels for micro-checker) - inductive per #434
        self.add_inductive(
            r"inductive MicroLevel : Type
| zero : MicroLevel
| succ : MicroLevel → MicroLevel
| max : MicroLevel → MicroLevel → MicroLevel
| imax : MicroLevel → MicroLevel → MicroLevel",
            "Micro-checker universe levels. Inductive structure mirrors kernel Level type \
             with zero, succ, max, and imax constructors.",
        )?;

        // MicroExpr type (expressions for micro-checker) - inductive per #431
        self.add_inductive(
            r"inductive MicroExpr : Type
| bvar : Nat → MicroExpr
| sort : MicroLevel → MicroExpr
| app : MicroExpr → MicroExpr → MicroExpr
| lam : MicroExpr → MicroExpr → MicroExpr
| pi : MicroExpr → MicroExpr → MicroExpr
| let_ : MicroExpr → MicroExpr → MicroExpr → MicroExpr
| opaque_ : MicroExpr → MicroExpr",
            "Micro-checker expression type. Inductive definition enables structural recursion \
             for micro_lift, micro_instantiate, micro_whnf, and kernel_to_micro.",
        )?;

        // =========================================================
        // PART 15: Micro-Checker Operations
        // =========================================================

        // nat_to_microlevel: Convert Nat universe level to MicroLevel
        self.add_recursive_def(
            r"def nat_to_microlevel (n : Nat) : MicroLevel := match n with
| Nat.zero => MicroLevel.zero
| Nat.succ m => MicroLevel.succ (nat_to_microlevel m)",
            "Convert natural number level to MicroLevel. Part of #516.",
        )?;

        // level_to_microlevel: Convert a full kernel Level (zero|succ|max|imax|param)
        // to the micro-checker's MicroLevel (zero|succ|max|imax). The param case has
        // no MicroLevel analogue, so it erases to MicroLevel.zero — consistent with the
        // bounded-opaque philosophy (kernel_to_micro already maps const heads to
        // MicroExpr.opaque_ (MicroExpr.sort MicroLevel.zero)). Levels promotion (task #29).
        self.add_recursive_def(
            r"def level_to_microlevel (l : Level) : MicroLevel := match l with
| Level.zero => MicroLevel.zero
| Level.succ m => MicroLevel.succ (level_to_microlevel m)
| Level.max a b => MicroLevel.max (level_to_microlevel a) (level_to_microlevel b)
| Level.imax a b => MicroLevel.imax (level_to_microlevel a) (level_to_microlevel b)
| Level.param _ => MicroLevel.zero",
            "Convert a full kernel Level to MicroLevel; param erases to zero (opaque). Part of #516, task #29 Levels promotion.",
        )?;

        // lift_bvar: helper for micro_lift bvar case
        self.add_recursive_def(
            r"def lift_bvar (idx : Nat) (cutoff : Nat) (amount : Nat) : Nat := Nat.rec (fun _ => Nat) (Nat.add idx amount) (fun _ _ => idx) (Nat.sub cutoff idx)",
            "Compute lifted bvar index: idx+amount if idx >= cutoff, else idx. Part of #441.",
        )?;

        // micro_lift: lift bound variables >= cutoff by amount
        self.add_recursive_def(
            r"def micro_lift (e : MicroExpr) (c : Nat) (n : Nat) : MicroExpr := match e with
| MicroExpr.bvar i => MicroExpr.bvar (lift_bvar i c n)
| MicroExpr.sort l => MicroExpr.sort l
| MicroExpr.app f a => MicroExpr.app (micro_lift f c n) (micro_lift a c n)
| MicroExpr.lam ty body => MicroExpr.lam (micro_lift ty c n) (micro_lift body (Nat.succ c) n)
| MicroExpr.pi ty body => MicroExpr.pi (micro_lift ty c n) (micro_lift body (Nat.succ c) n)
| MicroExpr.let_ ty val body => MicroExpr.let_ (micro_lift ty c n) (micro_lift val c n) (micro_lift body (Nat.succ c) n)
| MicroExpr.opaque_ ty => MicroExpr.opaque_ (micro_lift ty c n)",
            "Lift bound variables >= cutoff by amount. Constructive via MicroExpr.rec. Part of #441.",
        )?;

        // micro_instantiate_bvar_geq: helper for idx >= depth case
        self.add_recursive_def(
            r"def micro_instantiate_bvar_geq (idx : Nat) (depth : Nat) (val : MicroExpr) : MicroExpr := Nat.rec (fun _ => MicroExpr) (micro_lift val Nat.zero depth) (fun _ _ => MicroExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) (Nat.sub idx depth)",
            "Helper for micro_instantiate_at: handles idx >= depth case. Part of #647.",
        )?;

        // micro_instantiate_bvar_at: helper for bvar case
        self.add_recursive_def(
            r"def micro_instantiate_bvar_at (idx : Nat) (depth : Nat) (val : MicroExpr) : MicroExpr := Nat.rec (fun _ => MicroExpr) (micro_instantiate_bvar_geq idx depth val) (fun _ _ => MicroExpr.bvar idx) (Nat.sub depth idx)",
            "Helper for micro_instantiate_at: three-way comparison of idx vs depth. Part of #647.",
        )?;

        // micro_instantiate_at: substitute val for BVar depth, tracking binders
        self.add_recursive_def(
            r"def micro_instantiate_at (body : MicroExpr) (val : MicroExpr) (depth : Nat) : MicroExpr := match body with
| MicroExpr.bvar i => micro_instantiate_bvar_at i depth val
| MicroExpr.sort l => MicroExpr.sort l
| MicroExpr.app f a => MicroExpr.app (micro_instantiate_at f val depth) (micro_instantiate_at a val depth)
| MicroExpr.lam ty b => MicroExpr.lam (micro_instantiate_at ty val depth) (micro_instantiate_at b val (Nat.succ depth))
| MicroExpr.pi ty b => MicroExpr.pi (micro_instantiate_at ty val depth) (micro_instantiate_at b val (Nat.succ depth))
| MicroExpr.let_ ty v b => MicroExpr.let_ (micro_instantiate_at ty val depth) (micro_instantiate_at v val depth) (micro_instantiate_at b val (Nat.succ depth))
| MicroExpr.opaque_ ty => MicroExpr.opaque_ (micro_instantiate_at ty val depth)",
            "Substitute val for BVar depth in body. Constructive via MicroExpr.rec. Part of #647.",
        )?;

        // micro_instantiate: substitute val for BVar(0) (wrapper)
        self.add_recursive_def(
            r"def micro_instantiate (body : MicroExpr) (val : MicroExpr) : MicroExpr := micro_instantiate_at body val Nat.zero",
            "Substitute val for BVar(0) in body (wrapper for micro_instantiate_at). Part of #647.",
        )?;

        // whnf_app: helper for micro_whnf app case
        self.add_recursive_def(
            r"def whnf_app (f : MicroExpr) (a : MicroExpr) : MicroExpr := match f with
| MicroExpr.bvar _ => MicroExpr.app f a
| MicroExpr.sort _ => MicroExpr.app f a
| MicroExpr.app _ _ => MicroExpr.app f a
| MicroExpr.lam _ body => micro_instantiate body a
| MicroExpr.pi _ _ => MicroExpr.app f a
| MicroExpr.let_ _ _ _ => MicroExpr.app f a
| MicroExpr.opaque_ _ => MicroExpr.app f a",
            "Helper for micro_whnf app case. Beta-reduces if f is a lambda, \
             otherwise returns the application unchanged. Part of #441.",
        )?;

        // micro_whnf: weak head normal form (beta reduction only for now)
        self.add_recursive_def(
            r"def micro_whnf (e : MicroExpr) : MicroExpr := match e with
| MicroExpr.bvar i => MicroExpr.bvar i
| MicroExpr.sort l => MicroExpr.sort l
| MicroExpr.app f a => whnf_app f a
| MicroExpr.lam ty body => MicroExpr.lam ty body
| MicroExpr.pi ty body => MicroExpr.pi ty body
| MicroExpr.let_ ty val body => micro_instantiate body val
| MicroExpr.opaque_ ty => MicroExpr.opaque_ ty",
            "Weak head normal form. Performs beta reduction (app of lam) and \
             let reduction (zeta). Constructive via MicroExpr.rec. Part of #441.",
        )?;

        // micro_def_eq: definitional equality — REGISTRATION MOVED below the
        // `add_micro_structural_eq` block (Brick 3 of the micro-band drain). It
        // formerly registered here as a bare `MicroExpr -> MicroExpr -> Bool`
        // HelperAxiom; it now has a COMPUTABLE reducible body that depends on
        // `micro_structural_eq`, `micro_whnf_iter` and `micro_size`, so it must
        // register after them. See the block just after `add_micro_structural_eq`.

        // micro_structural_eq: structural (syntactic) equality on MicroExpr.
        //
        // Retired from a bare `-> Bool` HelperAxiom to a GENUINE recursive body
        // (Goal-2 DO-ALL). This is the ctor-wise syntactic equality: two
        // MicroExprs compare true iff they are identical syntax trees. It is the
        // MicroExpr analog of the proven `kexpr_beq` (kexpr_beq.rs) — same
        // two-level-recursor shape, no nested match, no self-recursion, no
        // `decide`/`native_decide`. The substrate (`micro_level_eqb`), the
        // function itself, the reflexivity metatheorem, and the non-vacuity
        // witnesses are all registered by `add_micro_structural_eq`.
        self.add_micro_structural_eq()?;

        // =========================================================
        // micro_def_eq GETS A BODY (Brick 3 of the micro-band drain).
        //
        // Formerly a bare `MicroExpr -> MicroExpr -> Bool` HelperAxiom, it is now
        // the reducible recursive definition
        //   micro_def_eq a b :=
        //     micro_structural_eq (micro_whnf_iter (micro_size a) a)
        //                         (micro_whnf_iter (micro_size b) b)
        // i.e. "structural equality AFTER weak-head normalisation", faithful to
        // the name's contract and to the real checker's `def_eq_impl` (whnf both
        // sides, then compare structurally). Giving it a body DRAINS it from the
        // axiom census AND refutes the false bridge `kernel_to_micro_def_eq`
        // (see micro_soundness.rs — the beta redex lives under a binder that
        // weak-head reduction never enters).
        //
        // HONEST SCOPE: `micro_def_eq` is UNTYPED, so NO fuel count is COMPLETE
        // (an Ω-like self-application never head-normalises). `micro_size` is a
        // sound, identity-safe fuel; on any closed strongly-normalising term the
        // checker forms it is more than enough, and completeness is neither
        // achieved nor needed — the deliverable is a computable body with
        // witnessed non-vacuity, NOT a micro-checker soundness claim.
        // =========================================================

        // micro_size: structural size of a MicroExpr (fuel bound for whnf_iter).
        self.add_recursive_def(
            r"def micro_size (e : MicroExpr) : Nat := match e with
| MicroExpr.bvar i => Nat.succ Nat.zero
| MicroExpr.sort l => Nat.succ Nat.zero
| MicroExpr.app f a => Nat.succ (Nat.add (micro_size f) (micro_size a))
| MicroExpr.lam ty body => Nat.succ (Nat.add (micro_size ty) (micro_size body))
| MicroExpr.pi ty body => Nat.succ (Nat.add (micro_size ty) (micro_size body))
| MicroExpr.let_ ty val body => Nat.succ (Nat.add (micro_size ty) (Nat.add (micro_size val) (micro_size body)))
| MicroExpr.opaque_ ty => Nat.succ (micro_size ty)",
            "Structural size of a MicroExpr (constructive via MicroExpr.rec). Used as a sound, \
             identity-safe fuel bound for micro_whnf_iter. Part of the micro-band drain (Brick 3).",
        )?;

        // micro_whnf_iter: iterate the single-step micro_whnf `n` times.
        // Nat.rec fold: n=0 returns e unchanged (identity-safe on non-redexes);
        // n = succ k applies one more micro_whnf on top of the k-fold. Because
        // MicroExpr is UNTYPED no fuel is COMPLETE (Ω-like terms never
        // head-normalise); none needs to be — see the block comment above.
        self.add_recursive_def(
            r"def micro_whnf_iter (n : Nat) (e : MicroExpr) : MicroExpr := Nat.rec (fun (_ : Nat) => MicroExpr) e (fun (_ : Nat) (acc : MicroExpr) => micro_whnf acc) n",
            "Iterate the single-step micro_whnf n times (Nat.rec fold). Identity at n=0; \
             fuel-incomplete on non-normalising terms (MicroExpr is untyped, so no fuel is \
             complete and none is needed). Part of the micro-band drain (Brick 3).",
        )?;

        // micro_def_eq: definitional equality = structural equality after WHNF.
        self.add_recursive_def(
            r"def micro_def_eq (a : MicroExpr) (b : MicroExpr) : Bool := micro_structural_eq (micro_whnf_iter (micro_size a) a) (micro_whnf_iter (micro_size b) b)",
            "Definitional equality on MicroExpr: weak-head-normalise BOTH sides (bounded by their \
             structural size) then compare structurally. Reducible body (drains the former \
             HelperAxiom); faithful to the name's 'structural after WHNF' contract. Part of the \
             micro-band drain (Brick 3).",
        )?;

        // Non-vacuity witnesses (masquerade guard): micro_def_eq is NOT
        // constantly-true, and its WHNF phase ACTUALLY FIRES. These kernel-check
        // ONLY because micro_def_eq genuinely computes.
        //   (1) distinct constructors -> false (both sides are already values).
        self.add_definition(SpecDefinition {
            name: "micro_def_eq_distinct_sort_bvar_false".to_string(),
            type_src: "Eq Bool (micro_def_eq (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar Nat.zero)) Bool.false".to_string(),
            value_src: Some("Eq.refl Bool Bool.false".to_string()),
            is_axiom: false,
            description: "micro_def_eq (sort 0) (bvar 0) = false: distinct constructors are not \
                def-eq. Non-vacuity witness (micro_def_eq is not constantly-true). Kernel-checked \
                by reduction. Part of the micro-band drain (Brick 3)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_def_eq".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        //   (2) REDUCTION-FIRING witness: a head redex on the LEFT that only
        //   agrees with the RHS AFTER a beta step — proves micro_whnf_iter
        //   genuinely reduces (the anti-"structural-only / const-true" guard).
        //   micro_def_eq (app (lam (sort 0) (bvar 0)) (sort 0)) (sort 0) = true:
        //   the LHS head-normalises (beta) to `sort 0`, matching the RHS; WITHOUT
        //   the whnf phase the app-vs-sort structural compare would be false.
        self.add_definition(SpecDefinition {
            name: "micro_def_eq_beta_fires_true".to_string(),
            type_src: concat!(
                "Eq Bool (micro_def_eq ",
                "(MicroExpr.app (MicroExpr.lam (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar Nat.zero)) (MicroExpr.sort MicroLevel.zero)) ",
                "(MicroExpr.sort MicroLevel.zero)) Bool.true",
            )
            .to_string(),
            value_src: Some("Eq.refl Bool Bool.true".to_string()),
            is_axiom: false,
            description: "micro_def_eq (app (lam (sort 0) (bvar 0)) (sort 0)) (sort 0) = true: the \
                LHS head-redex beta-reduces to sort 0 under micro_whnf_iter, so the two sides are \
                def-eq. REDUCTION-FIRING witness — proves the WHNF phase actually fires (without it \
                the app-vs-sort structural compare would be false). Part of the micro-band drain (Brick 3)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_def_eq".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // PART 16: Micro-Checker Certificate Types
        // =========================================================

        // MicroCert type - inductive per #440
        self.add_inductive(
            r"inductive MicroCert : Type
| sort : MicroLevel → MicroCert
| bvar : Nat → MicroExpr → MicroCert
| opaque_ : MicroExpr → MicroCert
| app : MicroCert → MicroCert → MicroExpr → MicroCert
| lam : MicroCert → MicroCert → MicroExpr → MicroCert
| pi : MicroCert → MicroLevel → MicroCert → MicroLevel → MicroCert
| let_ : MicroCert → MicroCert → MicroCert → MicroExpr → MicroCert",
            "Micro-checker proof certificate type. Inductive definition enables MicroCert.rec \
             for structural recursion in micro_verify and soundness proofs. Part of #440.",
        )?;

        // MicroCert_rec DELETED (micro-band vacuity exposure): this monomorphized
        // universe-Type-1 recursor axiom was consumed only by micro_verify_sound's
        // case-analysis proof. Since micro_has_type is now a TOTAL (degenerate)
        // predicate, micro_verify_sound is re-proved as a one-line totality corollary
        // (micro_has_type_total) that needs no case analysis — so this axiom is
        // consumer-free and removed. (Was a HelperAxiom carrying the "universe gap
        // blocks derivation" note; that note is now moot.)

        // micro_verify: verify certificate against expression
        self.add_recursive_def(
            r"def micro_verify (c : MicroCert) (e : MicroExpr) : MicroExpr := match c with
| MicroCert.sort l => MicroExpr.sort (MicroLevel.succ l)
| MicroCert.bvar i ty => ty
| MicroCert.opaque_ ty => ty
| MicroCert.app f a T => T
| MicroCert.lam A b T => T
| MicroCert.pi A l1 B l2 => MicroExpr.sort (MicroLevel.imax l1 l2)
| MicroCert.let_ A v b T => T",
            "Extract proven type from certificate. Constructive via MicroCert.rec. \
             The certificate encodes the type information for each expression form. \
             Part of #569.",
        )?;

        // =========================================================
        // PART 17: Micro-Checker Correctness Properties
        // =========================================================

        self.add_micro_lift_zero_id()?;

        // Instantiate BVar(0) gives the value
        // DerivedProved: equality chain mirroring the proven KExpr
        // instantiate_bvar_zero (whnf_lemmas.rs). The reduction is
        //   micro_instantiate (bvar 0) v
        //     =delta=  micro_instantiate_at (bvar 0) v 0
        //     =iota=   micro_instantiate_bvar_at 0 0 v
        //     =(Nat.rec, Nat.sub 0 0 = 0)=  micro_instantiate_bvar_geq 0 0 v
        //     =(Nat.rec, Nat.sub 0 0 = 0)=  micro_lift v Nat.zero Nat.zero
        //   and closes with micro_lift_zero_id v Nat.zero.
        //
        // Every reduction step from the LHS down to `micro_lift v 0 0` is
        // purely delta+iota on EXPLICIT `Nat.zero` constructors: the kernel
        // reduces `Nat.sub Nat.zero Nat.zero` to `Nat.zero`, then both
        // `Nat.rec` major premises are concrete `Nat.zero` and select the
        // base branches. (This is exactly why the symbolic-index KExpr lemma
        // instantiate_bvar_at_eq needed an explicit nat_sub_self rewrite while
        // this concrete-zero specialization does not.) So
        // `micro_instantiate (bvar 0) v` is definitionally equal to
        // `micro_lift v Nat.zero Nat.zero`, and the proof term is simply
        // `micro_lift_zero_id v Nat.zero`, whose type
        //   Eq MicroExpr (micro_lift v Nat.zero Nat.zero) v
        // is defeq to the target
        //   Eq MicroExpr (micro_instantiate (MicroExpr.bvar Nat.zero) v) v.
        //
        // axiom_deps = {} (micro_lift_zero_id is itself 0-axiom DerivedProved).
        // Part of Goal-2 sub-effort C.
        self.add_definition(SpecDefinition {
            name: "micro_instantiate_bvar_zero".to_string(),
            type_src: "forall (v : MicroExpr), Eq MicroExpr (micro_instantiate (MicroExpr.bvar Nat.zero) v) v".to_string(),
            value_src: Some(
                "fun (v : MicroExpr) => micro_lift_zero_id v Nat.zero".to_string(),
            ),
            is_axiom: false,
            description: "Instantiating BVar(0) gives the substituted value. DerivedProved: \
                micro_instantiate (bvar 0) v reduces by delta+iota (on explicit Nat.zero) to \
                micro_lift v 0 0, then micro_lift_zero_id closes it. Part of Goal-2 sub-effort C.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["micro_lift_zero_id".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // micro_instantiate on sort is identity
        self.add_definition(SpecDefinition {
            name: "micro_instantiate_sort".to_string(),
            type_src: "forall (l : MicroLevel) (val : MicroExpr), Eq MicroExpr (micro_instantiate (MicroExpr.sort l) val) (MicroExpr.sort l)".to_string(),
            value_src: Some("fun (l : MicroLevel) (val : MicroExpr) => Eq.refl MicroExpr (MicroExpr.sort l)".to_string()),
            is_axiom: false,
            description: "micro_instantiate (sort l) val = sort l. Derived by reduction. Part of #666.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // micro_instantiate over app — DerivedProved via direct Eq.refl.
        // micro_instantiate (app f a) val =delta= micro_instantiate_at (app f a) val 0
        // =iota(app match arm)= app (micro_instantiate_at f val 0) (micro_instantiate_at a val 0),
        // and the RHS app (micro_instantiate f val) (micro_instantiate a val) =delta(x2)=
        // the same term, so the two sides are kernel-defeq. Byte-for-byte MicroExpr copy of
        // the proven KExpr instantiate_at_app (whnf_lemmas.rs), whose old structural-
        // registration bypass now delegates to the fully-checked add_definition path.
        // Retires the #643 HelperAxiom. Part of #666, Goal-2 sub-effort C.
        self.add_definition(SpecDefinition {
            name: "micro_instantiate_app".to_string(),
            type_src: "forall (f : MicroExpr) (a : MicroExpr) (val : MicroExpr), Eq MicroExpr (micro_instantiate (MicroExpr.app f a) val) (MicroExpr.app (micro_instantiate f val) (micro_instantiate a val))".to_string(),
            value_src: Some("fun (f : MicroExpr) (a : MicroExpr) (val : MicroExpr) => Eq.refl MicroExpr (MicroExpr.app (micro_instantiate f val) (micro_instantiate a val))".to_string()),
            is_axiom: false,
            description: "micro_instantiate (app f a) val = app (micro_instantiate f val) (micro_instantiate a val). DerivedProved via Eq.refl (delta+iota defeq). Part of #666.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // micro_instantiate over lam — retired from HelperAxiom to DerivedProved.
        // Byte-for-byte mirror of the landed micro_instantiate_pi (lam<->pi).
        //   micro_instantiate (lam ty b) val
        //     =delta= micro_instantiate_at (lam ty b) val Nat.zero
        //     =iota=  lam (micro_instantiate_at ty val Nat.zero)
        //                (micro_instantiate_at b val (Nat.succ Nat.zero))
        // and the RHS's (micro_instantiate ty val) =delta= micro_instantiate_at
        // ty val Nat.zero, so Eq.refl on the depth-incremented body form checks.
        // value_src is a direct Eq.refl. Retires HelperAxiom; 0 axiom_deps.
        self.add_definition(SpecDefinition {
            name: "micro_instantiate_lam".to_string(),
            type_src: "forall (ty : MicroExpr) (b : MicroExpr) (val : MicroExpr), Eq MicroExpr (micro_instantiate (MicroExpr.lam ty b) val) (MicroExpr.lam (micro_instantiate ty val) (micro_instantiate_at b val (Nat.succ Nat.zero)))".to_string(),
            value_src: Some("fun (ty : MicroExpr) (b : MicroExpr) (val : MicroExpr) => Eq.refl MicroExpr (MicroExpr.lam (micro_instantiate ty val) (micro_instantiate_at b val (Nat.succ Nat.zero)))".to_string()),
            is_axiom: false,
            description: "micro_instantiate (lam ty b) val = lam (micro_instantiate ty val) (micro_instantiate_at b val 1). DerivedProved via Eq.refl (delta+iota reduction); byte-for-byte mirror of micro_instantiate_pi. Part of #666.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // micro_instantiate over pi — retired from HelperAxiom to DerivedProved.
        // Exact analog of the KExpr instantiate_at_pi/instantiate_pi proof
        // (whnf_lemmas.rs:191/248): both sides reduce to the same normal form.
        //   micro_instantiate (pi ty b) val
        //     =delta= micro_instantiate_at (pi ty b) val Nat.zero
        //     =iota=  pi (micro_instantiate_at ty val Nat.zero)
        //                (micro_instantiate_at b val (Nat.succ Nat.zero))
        // and the RHS's (micro_instantiate ty val) =delta= micro_instantiate_at
        // ty val Nat.zero, so Eq.refl on the depth-incremented body form checks.
        // value_src is a direct Eq.refl. Retires HelperAxiom; 0 axiom_deps.
        self.add_definition(SpecDefinition {
            name: "micro_instantiate_pi".to_string(),
            type_src: "forall (ty : MicroExpr) (b : MicroExpr) (val : MicroExpr), Eq MicroExpr (micro_instantiate (MicroExpr.pi ty b) val) (MicroExpr.pi (micro_instantiate ty val) (micro_instantiate_at b val (Nat.succ Nat.zero)))".to_string(),
            value_src: Some("fun (ty : MicroExpr) (b : MicroExpr) (val : MicroExpr) => Eq.refl MicroExpr (MicroExpr.pi (micro_instantiate ty val) (micro_instantiate_at b val (Nat.succ Nat.zero)))".to_string()),
            is_axiom: false,
            description: "micro_instantiate (pi ty b) val = pi (micro_instantiate ty val) (micro_instantiate_at b val 1). DerivedProved via Eq.refl (delta+iota reduction); exact analog of KExpr instantiate_at_pi. Part of #666.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // WHNF idempotence — TRUE single-step form (DerivedProved).
        //
        // SOUNDNESS FIX: the previous statement
        //   forall e, micro_whnf (micro_whnf e) = micro_whnf e
        // was FALSE-as-stated. `micro_whnf` is a SINGLE weak-head step (one beta
        // / one zeta), NOT a full normalizer: it does not re-normalize its own
        // output. So for a term whose ONE-step contractum is itself a redex,
        // applying `micro_whnf` twice reduces strictly further than once.
        // Counterexample:
        //   e = let_ T (lam A (bvar 0)) (app (bvar 0) (sort 0))
        // One step (zeta): micro_whnf e = micro_instantiate body val
        //   = app (lam A (bvar 0)) (sort 0)   -- still a redex.
        // A second step beta-reduces it, so micro_whnf (micro_whnf e) =/= micro_whnf e.
        // An `is_axiom:true` asserting that false equation is a latent soundness
        // smell.
        //
        // The TRUE single-step fact: micro_whnf IS idempotent on the head forms
        // it leaves unchanged — i.e. on already-weak-head-normal values. We
        // capture this with the lambda head form (the canonical output of a beta
        // step):
        //   forall ty body, micro_whnf (micro_whnf (lam ty body)) = micro_whnf (lam ty body)
        // Reduction (delta+iota, no axioms): micro_whnf (lam ty body) =iota= lam ty body
        // (the lam match arm returns it unchanged), so both sides reduce to
        // `lam ty body` and `Eq.refl` checks. (Analogous idempotence on sort/pi
        // holds identically; see micro_whnf_sort/lam/pi. The general unrestricted
        // statement is false and intentionally NOT claimed here.) The kernel
        // add_decl rejects this term unless it genuinely reduces — masquerade
        // guard. axiom_deps = {} (foundational closure).
        self.add_definition(SpecDefinition {
            name: "micro_whnf_idempotent".to_string(),
            type_src:
                "forall (ty : MicroExpr) (body : MicroExpr), Eq MicroExpr (micro_whnf (micro_whnf (MicroExpr.lam ty body))) (micro_whnf (MicroExpr.lam ty body))"
                    .to_string(),
            value_src: Some("fun (ty : MicroExpr) (body : MicroExpr) => Eq.refl MicroExpr (MicroExpr.lam ty body)".to_string()),
            is_axiom: false,
            description: "WHNF is idempotent on weak-head-normal forms: \
                micro_whnf (micro_whnf (lam ty body)) = micro_whnf (lam ty body). DerivedProved via \
                Eq.refl (both sides reduce to lam ty body by the lam match arm). micro_whnf is a \
                SINGLE step and is NOT idempotent in general — it does not re-normalize its output \
                (so the old unrestricted statement was false).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["micro_whnf".to_string(), "Eq.refl".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // WHNF preserves values
        // micro_whnf (sort l) = sort l by the match arm in micro_whnf.
        // Promoted from HelperAxiom to DerivedLemma with constructive Eq.refl proof.
        // Part of #3303: soundness audit — replace helper axioms with proof terms.
        self.add_definition(SpecDefinition {
            name: "micro_whnf_sort".to_string(),
            type_src: "forall (l : MicroLevel), Eq MicroExpr (micro_whnf (MicroExpr.sort l)) (MicroExpr.sort l)".to_string(),
            value_src: Some("fun (l : MicroLevel) => Eq.refl MicroExpr (MicroExpr.sort l)".to_string()),
            is_axiom: false,
            description: "Sorts are in WHNF. Derived by reduction: micro_whnf matches sort and returns it unchanged. Part of #3303.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // micro_whnf (lam ty body) = lam ty body by the match arm in micro_whnf.
        // Promoted from HelperAxiom to DerivedLemma with constructive Eq.refl proof.
        // Part of #3303: soundness audit — replace helper axioms with proof terms.
        self.add_definition(SpecDefinition {
            name: "micro_whnf_lam".to_string(),
            type_src: "forall (ty : MicroExpr) (body : MicroExpr), Eq MicroExpr (micro_whnf (MicroExpr.lam ty body)) (MicroExpr.lam ty body)".to_string(),
            value_src: Some("fun (ty : MicroExpr) (body : MicroExpr) => Eq.refl MicroExpr (MicroExpr.lam ty body)".to_string()),
            is_axiom: false,
            description: "Lambdas are in WHNF. Derived by reduction: micro_whnf matches lam and returns it unchanged. Part of #3303.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // micro_whnf (pi ty body) = pi ty body by the match arm in micro_whnf.
        // Promoted from HelperAxiom to DerivedLemma with constructive Eq.refl proof.
        // Part of #3303: soundness audit — replace helper axioms with proof terms.
        self.add_definition(SpecDefinition {
            name: "micro_whnf_pi".to_string(),
            type_src: "forall (ty : MicroExpr) (body : MicroExpr), Eq MicroExpr (micro_whnf (MicroExpr.pi ty body)) (MicroExpr.pi ty body)".to_string(),
            value_src: Some("fun (ty : MicroExpr) (body : MicroExpr) => Eq.refl MicroExpr (MicroExpr.pi ty body)".to_string()),
            is_axiom: false,
            description: "Pis are in WHNF. Derived by reduction: micro_whnf matches pi and returns it unchanged. Part of #3303.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // WHNF beta reduction — TRUE single-step contract (DerivedProved).
        //
        // SOUNDNESS FIX: the previous statement
        //   micro_whnf (app (lam ty body) arg) = micro_whnf (micro_instantiate body arg)
        // was FALSE-as-stated. `micro_whnf` is a SINGLE weak-head step: for an
        // application it calls `whnf_app`, which on `lam` returns exactly
        // `micro_instantiate body arg` WITHOUT re-normalizing the contractum.
        // The old RHS re-applied `micro_whnf` to that contractum, so the two
        // sides differ whenever `micro_instantiate body arg` is itself a redex
        // (e.g. body = app (lam _ (bvar 1)) (sort 0), arg = sort 0): the LHS
        // leaves the inner redex unreduced, the RHS beta-reduces it. An
        // `is_axiom:true` asserting that false equation is a latent soundness
        // smell.
        //
        // The TRUE single-step fact is that ONE weak-head step of the redex IS
        // the substituted body:
        //   micro_whnf (app (lam ty body) arg) = micro_instantiate body arg
        // Reduction chain (delta+iota, no axioms):
        //   micro_whnf (app (lam ty body) arg)
        //     =delta=  whnf_app (lam ty body) arg            (app match arm)
        //     =iota=   micro_instantiate body arg            (whnf_app lam arm)
        // so both sides are the same normal form and `Eq.refl` checks. The
        // kernel add_decl rejects this term unless it genuinely reduces — the
        // masquerade guard. axiom_deps = {} (foundational closure).
        self.add_definition(SpecDefinition {
            name: "micro_whnf_beta".to_string(),
            type_src: "forall (ty : MicroExpr) (body : MicroExpr) (arg : MicroExpr), Eq MicroExpr (micro_whnf (MicroExpr.app (MicroExpr.lam ty body) arg)) (micro_instantiate body arg)".to_string(),
            value_src: Some("fun (ty : MicroExpr) (body : MicroExpr) (arg : MicroExpr) => Eq.refl MicroExpr (micro_instantiate body arg)".to_string()),
            is_axiom: false,
            description: "WHNF performs ONE beta step: micro_whnf (app (lam ty body) arg) = \
                micro_instantiate body arg. DerivedProved via Eq.refl (delta: app arm -> whnf_app; \
                iota: whnf_app lam arm -> micro_instantiate). Single-step contract; micro_whnf does \
                NOT re-normalize the contractum (so the old recursive-whnf RHS was false).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_whnf".to_string(),
                "whnf_app".to_string(),
                "micro_instantiate".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // def_eq reflexivity — FLIPPED to a genuine theorem (Brick 3 of the
        // micro-band drain). `micro_def_eq e e` unfolds (delta) to
        // `micro_structural_eq X X` with `X = micro_whnf_iter (micro_size e) e`;
        // `micro_structural_eq_refl X` closes it up to defeq. Zero-axiom
        // (foundational closure through the already-proven structural refl).
        self.add_definition(SpecDefinition {
            name: "micro_def_eq_refl".to_string(),
            type_src: "forall (e : MicroExpr), Eq Bool (micro_def_eq e e) Bool.true".to_string(),
            value_src: Some(
                "fun (e : MicroExpr) => micro_structural_eq_refl (micro_whnf_iter (micro_size e) e)"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Definitional equality is reflexive. DerivedProved (Brick 3): micro_def_eq \
                e e = micro_structural_eq (micro_whnf_iter (micro_size e) e) (micro_whnf_iter \
                (micro_size e) e); micro_structural_eq_refl on that common normal form closes it. \
                Foundational closure."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_structural_eq_refl".to_string(),
                "micro_whnf_iter".to_string(),
                "micro_size".to_string(),
                "micro_def_eq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // def_eq symmetry — FLIPPED to a genuine theorem (Brick 4 of the
        // micro-band drain). `micro_def_eq a b` delta-unfolds to
        // `micro_structural_eq X Y` with X = micro_whnf_iter (micro_size a) a and
        // Y = micro_whnf_iter (micro_size b) b; `micro_def_eq b a` unfolds to
        // `micro_structural_eq Y X`. Per-side fuel keeps the definition symmetric
        // (the two normal forms X, Y are computed independently), so
        // `micro_structural_eq_symm X Y` closes it directly. Zero-axiom
        // (foundational closure through the argument-wise structural symmetry).
        self.add_definition(SpecDefinition {
            name: "micro_def_eq_symm".to_string(),
            type_src: "forall (a : MicroExpr) (b : MicroExpr), Eq Bool (micro_def_eq a b) (micro_def_eq b a)".to_string(),
            value_src: Some(
                "fun (a : MicroExpr) (b : MicroExpr) => micro_structural_eq_symm (micro_whnf_iter (micro_size a) a) (micro_whnf_iter (micro_size b) b)"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Definitional equality is symmetric. DerivedProved (Brick 4): \
                micro_def_eq a b = micro_structural_eq (micro_whnf_iter (micro_size a) a) \
                (micro_whnf_iter (micro_size b) b), and micro_def_eq b a = micro_structural_eq \
                (micro_whnf_iter (micro_size b) b) (micro_whnf_iter (micro_size a) a); \
                micro_structural_eq_symm on the two per-side normal forms closes it (per-side fuel \
                keeps the definition symmetric). Foundational closure. Vacuity exposure of a \
                computable equality, NOT micro-checker soundness."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_structural_eq_symm".to_string(),
                "micro_whnf_iter".to_string(),
                "micro_size".to_string(),
                "micro_def_eq".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Register the faithful `micro_structural_eq` — a GENUINE recursive
    /// structural (syntactic) boolean equality on `MicroExpr` — together with
    /// its universe-level substrate (`micro_level_eqb`), its reflexivity
    /// metatheorem (`micro_structural_eq_refl`), and non-vacuity witnesses that
    /// guard against a masquerade (it must reduce to `false` on distinct
    /// expressions, otherwise the witnesses would not kernel-check).
    ///
    /// This is the `MicroExpr` analog of the proven `kexpr_beq` (kexpr_beq.rs):
    /// two-level recursor dispatch, no nested match, no self-recursion, no
    /// `decide`/`native_decide`. All proofs are DerivedProved with an empty
    /// (foundational) axiom closure — they depend only on the freshly-proven
    /// helpers plus FoundationalRules (`MicroExpr.rec`, `MicroLevel.rec`,
    /// `nat_eqb`, `nat_is_zero`, `nat_sub_self`, `Bool.and`, `Eq.refl`,
    /// `Eq.cong`, `Eq.trans`).
    ///
    /// Substrate reused (registered earlier in the bundle):
    /// - `nat_eqb`, `nat_is_zero` (rec_env): boolean Nat equality.
    /// - `nat_sub_self` (foundation_types): `n - n = 0` (constructive).
    /// - `Bool.and`, `Bool.true`, `Bool.false` (kernel init_bool surface).
    /// - `Eq.refl`, `Eq.cong`, `Eq.trans` (foundation Eq rules).
    ///
    /// The `MicroExpr` constructor / recursor minor-premise order is
    /// `bvar, sort, app, lam, pi, let_, opaque_` (the same order the
    /// `micro_lift_zero_id` proof relies on). `MicroLevel` is
    /// `zero, succ, max, imax`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or kernel-check.
    fn add_micro_structural_eq(&mut self) -> Result<(), SpecError> {
        // micro_level_eqb: boolean equality on MicroLevel.
        // MicroLevel = zero | succ MicroLevel | max .. | imax ...
        // Outer MicroLevel.rec on the first level (motive `MicroLevel -> Bool`),
        // inner MicroLevel.rec dispatch on the second. Binary ctors (max/imax)
        // conjoin the two recursive-field IHs applied to the matching inner
        // fields. Exact analog of kexpr_beq.rs's `level_eqb`.
        self.add_recursive_def(
            concat!(
                "def micro_level_eqb (a : MicroLevel) (b : MicroLevel) : Bool := ",
                "MicroLevel.rec (fun (_ : MicroLevel) => MicroLevel -> Bool) ",
                // a = zero
                "(fun (y : MicroLevel) => MicroLevel.rec (fun (_ : MicroLevel) => Bool) ",
                "Bool.true ",
                "(fun (yp : MicroLevel) (_ : Bool) => Bool.false) ",
                "(fun (yl : MicroLevel) (yr : MicroLevel) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : MicroLevel) (yr : MicroLevel) (_ : Bool) (_ : Bool) => Bool.false) y) ",
                // a = succ ap  (ih_ap : MicroLevel -> Bool)
                "(fun (ap : MicroLevel) (ih_ap : MicroLevel -> Bool) => fun (y : MicroLevel) => ",
                "MicroLevel.rec (fun (_ : MicroLevel) => Bool) ",
                "Bool.false ",
                "(fun (yp : MicroLevel) (_ : Bool) => ih_ap yp) ",
                "(fun (yl : MicroLevel) (yr : MicroLevel) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : MicroLevel) (yr : MicroLevel) (_ : Bool) (_ : Bool) => Bool.false) y) ",
                // a = max al ar  (ih_al ih_ar : MicroLevel -> Bool)
                "(fun (al : MicroLevel) (ar : MicroLevel) (ih_al : MicroLevel -> Bool) (ih_ar : MicroLevel -> Bool) => ",
                "fun (y : MicroLevel) => MicroLevel.rec (fun (_ : MicroLevel) => Bool) ",
                "Bool.false ",
                "(fun (yp : MicroLevel) (_ : Bool) => Bool.false) ",
                "(fun (yl : MicroLevel) (yr : MicroLevel) (_ : Bool) (_ : Bool) => Bool.and (ih_al yl) (ih_ar yr)) ",
                "(fun (yl : MicroLevel) (yr : MicroLevel) (_ : Bool) (_ : Bool) => Bool.false) y) ",
                // a = imax al ar  (ih_al ih_ar : MicroLevel -> Bool)
                "(fun (al : MicroLevel) (ar : MicroLevel) (ih_al : MicroLevel -> Bool) (ih_ar : MicroLevel -> Bool) => ",
                "fun (y : MicroLevel) => MicroLevel.rec (fun (_ : MicroLevel) => Bool) ",
                "Bool.false ",
                "(fun (yp : MicroLevel) (_ : Bool) => Bool.false) ",
                "(fun (yl : MicroLevel) (yr : MicroLevel) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (yl : MicroLevel) (yr : MicroLevel) (_ : Bool) (_ : Bool) => Bool.and (ih_al yl) (ih_ar yr)) y) ",
                "a b",
            ),
            "Boolean equality on micro-checker universe levels \
             (MicroLevel = zero|succ|max|imax). Two-level MicroLevel.rec dispatch \
             (no nested match). Sort-arm substrate for micro_structural_eq. \
             Analog of kexpr_beq.rs's level_eqb.",
        )?;

        // micro_structural_eq: structural boolean equality on MicroExpr.
        //
        // Outer MicroExpr.rec on the first expression (motive `MicroExpr -> Bool`),
        // inner MicroExpr.rec dispatch on the second. Each constructor compares
        // its payload: bvar via nat_eqb; sort via micro_level_eqb; app/lam/pi
        // conjoin the two recursive-subterm IHs (Bool.and) applied to the
        // matching inner subterms; let_ conjoins all three; opaque_ compares its
        // single subterm. All cross-constructor pairs are false. This is a
        // GENUINE syntactic equality (the *_false witnesses below witness it).
        //
        // MicroExpr.rec minor-premise order: bvar, sort, app, lam, pi, let_,
        // opaque_. For the inner (motive `_ => Bool`) recursor the recursive
        // fields still carry an IH slot (here ignored as `(_ : Bool)`).
        self.add_recursive_def(
            concat!(
                "def micro_structural_eq (a : MicroExpr) (b : MicroExpr) : Bool := ",
                "MicroExpr.rec (fun (_ : MicroExpr) => MicroExpr -> Bool) ",
                // a = bvar i
                "(fun (i : Nat) => fun (y : MicroExpr) => MicroExpr.rec (fun (_ : MicroExpr) => Bool) ",
                "(fun (j : Nat) => nat_eqb i j) ",
                "(fun (m : MicroLevel) => Bool.false) ",
                "(fun (g : MicroExpr) (c : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (v : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (_ : Bool) => Bool.false) y) ",
                // a = sort l
                "(fun (l : MicroLevel) => fun (y : MicroExpr) => MicroExpr.rec (fun (_ : MicroExpr) => Bool) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (m : MicroLevel) => micro_level_eqb l m) ",
                "(fun (g : MicroExpr) (c : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (v : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (_ : Bool) => Bool.false) y) ",
                // a = app f a1  (ih_f ih_a : MicroExpr -> Bool)
                "(fun (f : MicroExpr) (a1 : MicroExpr) (ih_f : MicroExpr -> Bool) (ih_a : MicroExpr -> Bool) => ",
                "fun (y : MicroExpr) => MicroExpr.rec (fun (_ : MicroExpr) => Bool) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (m : MicroLevel) => Bool.false) ",
                "(fun (g : MicroExpr) (c : MicroExpr) (_ : Bool) (_ : Bool) => Bool.and (ih_f g) (ih_a c)) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (v : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (_ : Bool) => Bool.false) y) ",
                // a = lam ty1 b1  (ih_ty ih_b : MicroExpr -> Bool)
                "(fun (ty1 : MicroExpr) (b1 : MicroExpr) (ih_ty : MicroExpr -> Bool) (ih_b : MicroExpr -> Bool) => ",
                "fun (y : MicroExpr) => MicroExpr.rec (fun (_ : MicroExpr) => Bool) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (m : MicroLevel) => Bool.false) ",
                "(fun (g : MicroExpr) (c : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.and (ih_ty t) (ih_b d)) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (v : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (_ : Bool) => Bool.false) y) ",
                // a = pi ty1 b1  (ih_ty ih_b : MicroExpr -> Bool)
                "(fun (ty1 : MicroExpr) (b1 : MicroExpr) (ih_ty : MicroExpr -> Bool) (ih_b : MicroExpr -> Bool) => ",
                "fun (y : MicroExpr) => MicroExpr.rec (fun (_ : MicroExpr) => Bool) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (m : MicroLevel) => Bool.false) ",
                "(fun (g : MicroExpr) (c : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.and (ih_ty t) (ih_b d)) ",
                "(fun (t : MicroExpr) (v : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (_ : Bool) => Bool.false) y) ",
                // a = let_ ty1 v1 b1  (ih_ty ih_v ih_b : MicroExpr -> Bool)
                "(fun (ty1 : MicroExpr) (v1 : MicroExpr) (b1 : MicroExpr) (ih_ty : MicroExpr -> Bool) (ih_v : MicroExpr -> Bool) (ih_b : MicroExpr -> Bool) => ",
                "fun (y : MicroExpr) => MicroExpr.rec (fun (_ : MicroExpr) => Bool) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (m : MicroLevel) => Bool.false) ",
                "(fun (g : MicroExpr) (c : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (v : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.and (ih_ty t) (Bool.and (ih_v v) (ih_b d))) ",
                "(fun (t : MicroExpr) (_ : Bool) => Bool.false) y) ",
                // a = opaque_ ty1  (ih_ty : MicroExpr -> Bool)
                "(fun (ty1 : MicroExpr) (ih_ty : MicroExpr -> Bool) => ",
                "fun (y : MicroExpr) => MicroExpr.rec (fun (_ : MicroExpr) => Bool) ",
                "(fun (j : Nat) => Bool.false) ",
                "(fun (m : MicroLevel) => Bool.false) ",
                "(fun (g : MicroExpr) (c : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (v : MicroExpr) (d : MicroExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) ",
                "(fun (t : MicroExpr) (_ : Bool) => ih_ty t) y) ",
                "a b",
            ),
            "Structural boolean equality on MicroExpr \
             (bvar|sort|app|lam|pi|let_|opaque_). Two-level MicroExpr.rec \
             dispatch: bvar via nat_eqb, sort via micro_level_eqb, app/lam/pi/ \
             let_ via Bool.and of subterm equalities, opaque_ via its subterm. \
             A genuine syntactic equality; the MicroExpr analog of kexpr_beq.",
        )?;

        // micro_nat_eqb_refl: nat_eqb n n = true (self-contained copy of
        // kexpr_beq.rs's nat_eqb_refl — that one lives only in the test-only
        // kexpr_beq beachhead, not in this bundle, so micro_structural_eq_refl
        // cannot depend on it).
        //
        // nat_eqb n n = nat_is_zero (Nat.add (Nat.sub n n) (Nat.sub n n)).
        // Transport nat_sub_self n : Nat.sub n n = 0 through
        // `fun s => nat_is_zero (Nat.add s s)`: at s = 0 the body is defeq to
        // nat_is_zero 0 = true (Nat.add x 0 reduces to x), so one Eq.cong closes
        // it up to defeq.
        self.add_definition(SpecDefinition {
            name: "micro_nat_eqb_refl".to_string(),
            type_src: "forall (n : Nat), Eq Bool (nat_eqb n n) Bool.true".to_string(),
            value_src: Some(
                concat!(
                    "fun (n : Nat) => ",
                    "Eq.cong Nat Bool ",
                    "(fun (s : Nat) => nat_is_zero (Nat.add s s)) ",
                    "(Nat.sub n n) Nat.zero ",
                    "(nat_sub_self n)",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "nat_eqb n n = true. DerivedProved via Eq.cong transport of nat_sub_self \
                through nat_is_zero (Nat.add s s). Foundational closure. Self-contained copy of \
                kexpr_beq's nat_eqb_refl for the micro_checker bundle."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "nat_sub_self".to_string(),
                "nat_is_zero".to_string(),
                "nat_eqb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // micro_level_eqb_refl: micro_level_eqb a a = true, by MicroLevel.rec
        // induction. Same shape as kexpr_beq.rs's level_eqb_refl.
        // - zero: Eq.refl.
        // - succ p: micro_level_eqb (succ p) (succ p) = micro_level_eqb p p; IH.
        // - max/imax l r: = Bool.and (..l l) (..r r); rewrite the left via IH
        //   (Eq.cong), residual Bool.and true (..r r) reduces to (..r r), IH closes.
        self.add_definition(SpecDefinition {
            name: "micro_level_eqb_refl".to_string(),
            type_src: "forall (a : MicroLevel), Eq Bool (micro_level_eqb a a) Bool.true"
                .to_string(),
            value_src: Some(
                concat!(
                    "fun (a : MicroLevel) => MicroLevel.rec ",
                    "(fun (z : MicroLevel) => Eq Bool (micro_level_eqb z z) Bool.true) ",
                    // zero
                    "(Eq.refl Bool Bool.true) ",
                    // succ p : ih
                    "(fun (p : MicroLevel) (ih : Eq Bool (micro_level_eqb p p) Bool.true) => ih) ",
                    // max l r : ih_l, ih_r
                    "(fun (l : MicroLevel) (r : MicroLevel) ",
                    "(ih_l : Eq Bool (micro_level_eqb l l) Bool.true) ",
                    "(ih_r : Eq Bool (micro_level_eqb r r) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(micro_level_eqb (MicroLevel.max l r) (MicroLevel.max l r)) ",
                    "(Bool.and Bool.true (micro_level_eqb r r)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bl : Bool) => Bool.and bl (micro_level_eqb r r)) ",
                    "(micro_level_eqb l l) Bool.true ih_l) ",
                    "ih_r) ",
                    // imax l r : ih_l, ih_r
                    "(fun (l : MicroLevel) (r : MicroLevel) ",
                    "(ih_l : Eq Bool (micro_level_eqb l l) Bool.true) ",
                    "(ih_r : Eq Bool (micro_level_eqb r r) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(micro_level_eqb (MicroLevel.imax l r) (MicroLevel.imax l r)) ",
                    "(Bool.and Bool.true (micro_level_eqb r r)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bl : Bool) => Bool.and bl (micro_level_eqb r r)) ",
                    "(micro_level_eqb l l) Bool.true ih_l) ",
                    "ih_r) ",
                    "a",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "micro_level_eqb a a = true, by MicroLevel.rec induction. DerivedProved, \
                foundational closure."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroLevel.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "micro_level_eqb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // micro_structural_eq_refl: forall e, micro_structural_eq e e = true.
        // THE reflexivity metatheorem, by MicroExpr.rec induction over the 7
        // constructors. Same proof shape as kexpr_beq.rs's kexpr_beq_refl:
        // - bvar i  : = nat_eqb i i; micro_nat_eqb_refl i.
        // - sort l  : = micro_level_eqb l l; micro_level_eqb_refl l.
        // - app/lam/pi : = Bool.and (..x x) (..y y); rewrite left IH (Eq.cong),
        //   residual Bool.and true _ reduces, right IH closes.
        // - let_ ty v b : = Bool.and (..ty ty) (Bool.and (..v v) (..b b)); rewrite
        //   ty via ih_ty -> Bool.and true (Bool.and (..v v) (..b b)) reduces to
        //   Bool.and (..v v) (..b b); then rewrite v via ih_v -> Bool.and true
        //   (..b b) reduces to (..b b); ih_b closes.
        // - opaque_ ty : = micro_structural_eq ty ty; ih_ty closes directly.
        self.add_definition(SpecDefinition {
            name: "micro_structural_eq_refl".to_string(),
            type_src:
                "forall (e : MicroExpr), Eq Bool (micro_structural_eq e e) Bool.true".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : MicroExpr) => MicroExpr.rec ",
                    "(fun (z : MicroExpr) => Eq Bool (micro_structural_eq z z) Bool.true) ",
                    // bvar i
                    "(fun (i : Nat) => micro_nat_eqb_refl i) ",
                    // sort l
                    "(fun (l : MicroLevel) => micro_level_eqb_refl l) ",
                    // app f a : ih_f, ih_a
                    "(fun (f : MicroExpr) (a : MicroExpr) ",
                    "(ih_f : Eq Bool (micro_structural_eq f f) Bool.true) ",
                    "(ih_a : Eq Bool (micro_structural_eq a a) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(micro_structural_eq (MicroExpr.app f a) (MicroExpr.app f a)) ",
                    "(Bool.and Bool.true (micro_structural_eq a a)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bf : Bool) => Bool.and bf (micro_structural_eq a a)) ",
                    "(micro_structural_eq f f) Bool.true ih_f) ",
                    "ih_a) ",
                    // lam ty b : ih_ty, ih_b
                    "(fun (ty : MicroExpr) (b : MicroExpr) ",
                    "(ih_ty : Eq Bool (micro_structural_eq ty ty) Bool.true) ",
                    "(ih_b : Eq Bool (micro_structural_eq b b) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(micro_structural_eq (MicroExpr.lam ty b) (MicroExpr.lam ty b)) ",
                    "(Bool.and Bool.true (micro_structural_eq b b)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bt : Bool) => Bool.and bt (micro_structural_eq b b)) ",
                    "(micro_structural_eq ty ty) Bool.true ih_ty) ",
                    "ih_b) ",
                    // pi ty b : ih_ty, ih_b
                    "(fun (ty : MicroExpr) (b : MicroExpr) ",
                    "(ih_ty : Eq Bool (micro_structural_eq ty ty) Bool.true) ",
                    "(ih_b : Eq Bool (micro_structural_eq b b) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(micro_structural_eq (MicroExpr.pi ty b) (MicroExpr.pi ty b)) ",
                    "(Bool.and Bool.true (micro_structural_eq b b)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bt : Bool) => Bool.and bt (micro_structural_eq b b)) ",
                    "(micro_structural_eq ty ty) Bool.true ih_ty) ",
                    "ih_b) ",
                    // let_ ty v b : ih_ty, ih_v, ih_b
                    "(fun (ty : MicroExpr) (v : MicroExpr) (b : MicroExpr) ",
                    "(ih_ty : Eq Bool (micro_structural_eq ty ty) Bool.true) ",
                    "(ih_v : Eq Bool (micro_structural_eq v v) Bool.true) ",
                    "(ih_b : Eq Bool (micro_structural_eq b b) Bool.true) => ",
                    "Eq.trans Bool ",
                    "(micro_structural_eq (MicroExpr.let_ ty v b) (MicroExpr.let_ ty v b)) ",
                    "(Bool.and (micro_structural_eq v v) (micro_structural_eq b b)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bt : Bool) => Bool.and bt (Bool.and (micro_structural_eq v v) (micro_structural_eq b b))) ",
                    "(micro_structural_eq ty ty) Bool.true ih_ty) ",
                    "(Eq.trans Bool ",
                    "(Bool.and (micro_structural_eq v v) (micro_structural_eq b b)) ",
                    "(Bool.and Bool.true (micro_structural_eq b b)) ",
                    "Bool.true ",
                    "(Eq.cong Bool Bool ",
                    "(fun (bv : Bool) => Bool.and bv (micro_structural_eq b b)) ",
                    "(micro_structural_eq v v) Bool.true ih_v) ",
                    "ih_b)) ",
                    // opaque_ ty : ih_ty
                    "(fun (ty : MicroExpr) ",
                    "(ih_ty : Eq Bool (micro_structural_eq ty ty) Bool.true) => ih_ty) ",
                    "e",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "micro_structural_eq e e = true for all MicroExpr e, by MicroExpr.rec \
                structural induction over the 7 constructors. The reflexivity metatheorem for the \
                micro-checker's structural equality. DerivedProved, foundational closure.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroExpr.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "micro_structural_eq".to_string(),
                "micro_nat_eqb_refl".to_string(),
                "micro_level_eqb_refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Non-vacuity witnesses (masquerade guard): micro_structural_eq is NOT
        // constantly-true. These kernel-check ONLY because micro_structural_eq
        // genuinely reduces to `false` on distinct expressions. They are the
        // anti-masquerade evidence that the body captures real meaning.
        // =========================================================

        // sort 0 vs bvar 0 : different constructors -> false.
        self.add_definition(SpecDefinition {
            name: "micro_structural_eq_distinct_sort_bvar_false".to_string(),
            type_src: "Eq Bool (micro_structural_eq (MicroExpr.sort MicroLevel.zero) (MicroExpr.bvar Nat.zero)) Bool.false".to_string(),
            value_src: Some("Eq.refl Bool Bool.false".to_string()),
            is_axiom: false,
            description: "micro_structural_eq (sort 0) (bvar 0) = false: distinct constructors \
                compare unequal. Non-vacuity witness (micro_structural_eq is not constantly-true). \
                Kernel-checked by reduction.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_structural_eq".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // app (bvar 0) (bvar 0) vs lam (bvar 0) (bvar 0) : distinct constructors,
        // identical payloads -> false.
        self.add_definition(SpecDefinition {
            name: "micro_structural_eq_distinct_app_lam_false".to_string(),
            type_src: concat!(
                "Eq Bool (micro_structural_eq ",
                "(MicroExpr.app (MicroExpr.bvar Nat.zero) (MicroExpr.bvar Nat.zero)) ",
                "(MicroExpr.lam (MicroExpr.bvar Nat.zero) (MicroExpr.bvar Nat.zero))) Bool.false",
            )
            .to_string(),
            value_src: Some("Eq.refl Bool Bool.false".to_string()),
            is_axiom: false,
            description:
                "micro_structural_eq (app ..) (lam ..) = false: distinct constructors with \
                identical payloads still compare unequal. Non-vacuity witness. Kernel-checked by \
                reduction."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_structural_eq".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // bvar 0 vs bvar 1 : same constructor, distinct payload -> false (genuine
        // payload comparison, not just constructor tag).
        self.add_definition(SpecDefinition {
            name: "micro_structural_eq_distinct_bvar_index_false".to_string(),
            type_src: "Eq Bool (micro_structural_eq (MicroExpr.bvar Nat.zero) (MicroExpr.bvar (Nat.succ Nat.zero))) Bool.false".to_string(),
            value_src: Some("Eq.refl Bool Bool.false".to_string()),
            is_axiom: false,
            description: "micro_structural_eq (bvar 0) (bvar 1) = false: same constructor, distinct \
                de Bruijn index compares unequal (genuine payload comparison, not just constructor \
                tag). Non-vacuity witness. Kernel-checked by reduction.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "micro_structural_eq".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ================================================================
        // Symmetry metatheorems (Brick 4 of the micro-band drain): the
        // substrate for flipping the `micro_def_eq_symm` axiom to a genuine
        // theorem. `nat_eqb_symm` and `micro_level_eqb_symm` feed the diagonal
        // arms of `micro_structural_eq_symm`, which is the argument-wise
        // symmetry of the structural (post-whnf) equality. All DerivedProved,
        // foundational closure (no axiom deps).
        // ================================================================

        // nat_eqb_symm: nat_eqb i j = nat_eqb j i.
        // nat_eqb a b delta-unfolds to nat_is_zero (Nat.add (Nat.sub a b)
        // (Nat.sub b a)); swapping i,j only swaps the two Nat.add summands, so
        // nat_add_comm transported through nat_is_zero closes it up to defeq.
        self.add_definition(SpecDefinition {
            name: "nat_eqb_symm".to_string(),
            type_src: "forall (i : Nat) (j : Nat), Eq Bool (nat_eqb i j) (nat_eqb j i)".to_string(),
            value_src: Some(
                concat!(
                    "fun (i : Nat) (j : Nat) => ",
                    "Eq.cong Nat Bool (fun (s : Nat) => nat_is_zero s) ",
                    "(Nat.add (Nat.sub i j) (Nat.sub j i)) ",
                    "(Nat.add (Nat.sub j i) (Nat.sub i j)) ",
                    "(nat_add_comm (Nat.sub i j) (Nat.sub j i))",
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "nat_eqb i j = nat_eqb j i. DerivedProved via Eq.cong transport of \
                nat_add_comm through nat_is_zero (nat_eqb unfolds to a symmetric-modulo-add-comm \
                nat_is_zero of Nat.add of the two subtractions). Foundational closure. Part of the \
                micro-band drain (Brick 4)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "nat_is_zero".to_string(),
                "nat_add_comm".to_string(),
                "nat_eqb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // micro_level_eqb_symm: micro_level_eqb a b = micro_level_eqb b a
        // (4x4 double MicroLevel.rec; see micro_level_eqb_symm_value_src).
        self.add_definition(SpecDefinition {
            name: "micro_level_eqb_symm".to_string(),
            type_src: "forall (a : MicroLevel) (b : MicroLevel), Eq Bool (micro_level_eqb a b) \
                (micro_level_eqb b a)"
                .to_string(),
            value_src: Some(Self::micro_level_eqb_symm_value_src()),
            is_axiom: false,
            description: "micro_level_eqb a b = micro_level_eqb b a, by double MicroLevel.rec \
                (b-universalized outer motive). DerivedProved, foundational closure. Part of the \
                micro-band drain (Brick 4)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroLevel.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "micro_level_eqb".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // micro_structural_eq_symm: micro_structural_eq a b = micro_structural_eq
        // b a (7x7 double MicroExpr.rec; see micro_structural_eq_symm_value_src).
        // Diagonal arms use nat_eqb_symm (bvar), micro_level_eqb_symm (sort), the
        // outer IHs + Bool.and congruence (app/lam/pi/let_/opaque_); all 42
        // cross-constructor pairs reduce to Bool.false.
        self.add_definition(SpecDefinition {
            name: "micro_structural_eq_symm".to_string(),
            type_src: "forall (a : MicroExpr) (b : MicroExpr), Eq Bool (micro_structural_eq a b) \
                (micro_structural_eq b a)"
                .to_string(),
            value_src: Some(Self::micro_structural_eq_symm_value_src()),
            is_axiom: false,
            description: "micro_structural_eq a b = micro_structural_eq b a for all MicroExpr, by \
                double MicroExpr.rec (b-universalized outer motive). Diagonal arms close by \
                nat_eqb_symm / micro_level_eqb_symm / Bool.and congruence over the outer IHs; the \
                42 cross-constructor pairs reduce to false. DerivedProved, foundational closure. \
                Part of the micro-band drain (Brick 4)."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroExpr.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "micro_structural_eq".to_string(),
                "nat_eqb_symm".to_string(),
                "micro_level_eqb_symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Register `micro_lift_zero_id` (lifting by amount 0 is identity) as a
    /// genuine kernel-checked, zero-axiom theorem, together with the two
    /// supporting arithmetic/bvar lemmas it needs.
    ///
    /// Mirrors the proven KExpr `lift_at_amount_zero` (expr_model_lift_lemmas/
    /// amount_zero.rs): `MicroExpr.rec` structural induction with a
    /// cutoff-universalized motive, closing each constructor branch by
    /// `Eq.cong` over the induction hypotheses. The bvar branch appeals to
    /// `micro_lift_bvar_amount_zero` (lift_bvar i c 0 = i), which in turn is a
    /// `Nat.rec`-constant fact (`micro_nat_rec_const`).
    ///
    /// All dependencies are FoundationalRules (Nat.rec, MicroExpr.rec, Eq.refl,
    /// Eq.cong, Eq.trans) or these freshly-proven lemmas — axiom_deps = {}.
    /// Part of Goal-2 sub-effort C.
    fn add_micro_lift_zero_id(&mut self) -> Result<(), SpecError> {
        // micro_nat_rec_const: Nat.rec with constant Nat branches returns the
        // constant value. Nat-valued analogue of the KExpr `nat_rec_const`.
        self.add_definition(SpecDefinition {
            name: "micro_nat_rec_const".to_string(),
            type_src: "forall (v : Nat) (n : Nat), Eq Nat (Nat.rec (fun (_ : Nat) => Nat) v (fun (_ : Nat) (_ : Nat) => v) n) v".to_string(),
            value_src: Some(concat!(
                "fun (v : Nat) (n : Nat) => Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.rec (fun (_ : Nat) => Nat) v (fun (_ : Nat) (_ : Nat) => v) k) v) ",
                "(Eq.refl Nat v) ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.rec (fun (_ : Nat) => Nat) v (fun (_ : Nat) (_ : Nat) => v) k) v) => ",
                "Eq.refl Nat v) ",
                "n",
            ).to_string()),
            is_axiom: false,
            description: "Nat.rec with constant Nat branches always returns the constant. \
                DerivedProved via Nat.rec induction (both branches refl). Part of Goal-2 sub-effort C.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // micro_lift_bvar_amount_zero: lifting a bvar index by amount 0 is the
        // identity on the index. `lift_bvar i c 0` delta-unfolds to
        //   Nat.rec (fun _ => Nat) (Nat.add i 0) (fun _ _ => i) (Nat.sub c i)
        // and `Nat.add i 0` reduces to `i`, so both branches are `i`; the
        // constant-rec lemma applies directly.
        self.add_definition(SpecDefinition {
            name: "micro_lift_bvar_amount_zero".to_string(),
            type_src: "forall (i : Nat) (c : Nat), Eq Nat (lift_bvar i c Nat.zero) i".to_string(),
            value_src: Some(
                "fun (i : Nat) (c : Nat) => micro_nat_rec_const i (Nat.sub c i)".to_string(),
            ),
            is_axiom: false,
            description: "Lifting a bvar index by amount 0 is identity. DerivedProved via \
                micro_nat_rec_const (Nat.add i 0 reduces to i). Part of Goal-2 sub-effort C."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["micro_nat_rec_const".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // micro_lift_zero_id: lifting any MicroExpr by amount 0 is identity.
        //
        // MicroExpr.rec structural induction with a cutoff-universalized motive
        //   fun e => forall (c : Nat), Eq MicroExpr (micro_lift e c Nat.zero) e
        // The recursor's minor premises follow the constructor order
        //   bvar, sort, app, lam, pi, let_, opaque_.
        // micro_lift is a Definition (reducible), so `micro_lift (C ...) c 0`
        // delta+iota-reduces to its constructor body; each branch rebuilds the
        // constructor and rewrites every sub-expression via its IH. lam/pi/let_
        // bodies recurse under a binder, so their IH is applied at Nat.succ c.
        self.add_definition(SpecDefinition {
            name: "micro_lift_zero_id".to_string(),
            type_src: "forall (e : MicroExpr) (c : Nat), Eq MicroExpr (micro_lift e c Nat.zero) e"
                .to_string(),
            value_src: Some(Self::micro_lift_zero_id_value_src()),
            is_axiom: false,
            description: "Lifting by 0 is identity. DerivedProved via MicroExpr.rec structural \
                induction with cutoff-universalized motive + micro_lift_bvar_amount_zero. \
                Part of Goal-2 sub-effort C."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "MicroExpr.rec".to_string(),
                "micro_lift_bvar_amount_zero".to_string(),
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Proof term for `micro_lift_zero_id`. Factored out to keep the line
    /// length and the `concat!` chain readable.
    fn micro_lift_zero_id_value_src() -> String {
        concat!(
            "fun (e : MicroExpr) (c : Nat) => ",
            "MicroExpr.rec ",
            // motive: universalize cutoff so lam/pi/let_ IHs work at Nat.succ c
            "(fun (e : MicroExpr) => forall (c : Nat), Eq MicroExpr (micro_lift e c Nat.zero) e) ",
            // bvar branch: micro_lift (bvar i) c 0 = bvar (lift_bvar i c 0) = bvar i
            "(fun (i : Nat) (c : Nat) => ",
            "Eq.cong Nat MicroExpr MicroExpr.bvar ",
            "(lift_bvar i c Nat.zero) i (micro_lift_bvar_amount_zero i c)) ",
            // sort branch: micro_lift (sort l) c 0 = sort l by match reduction
            "(fun (l : MicroLevel) (c : Nat) => Eq.refl MicroExpr (MicroExpr.sort l)) ",
            // app branch
            "(fun (f : MicroExpr) (a : MicroExpr) ",
            "(ih_f : forall (c : Nat), Eq MicroExpr (micro_lift f c Nat.zero) f) ",
            "(ih_a : forall (c : Nat), Eq MicroExpr (micro_lift a c Nat.zero) a) ",
            "(c : Nat) => ",
            "Eq.trans MicroExpr ",
            "(micro_lift (MicroExpr.app f a) c Nat.zero) ",
            "(MicroExpr.app f (micro_lift a c Nat.zero)) ",
            "(MicroExpr.app f a) ",
            "(Eq.cong MicroExpr MicroExpr ",
            "(fun (x : MicroExpr) => MicroExpr.app x (micro_lift a c Nat.zero)) ",
            "(micro_lift f c Nat.zero) f (ih_f c)) ",
            "(Eq.cong MicroExpr MicroExpr ",
            "(fun (x : MicroExpr) => MicroExpr.app f x) ",
            "(micro_lift a c Nat.zero) a (ih_a c))) ",
            // lam branch (body recurses at Nat.succ c)
            "(fun (ty : MicroExpr) (body : MicroExpr) ",
            "(ih_ty : forall (c : Nat), Eq MicroExpr (micro_lift ty c Nat.zero) ty) ",
            "(ih_body : forall (c : Nat), Eq MicroExpr (micro_lift body c Nat.zero) body) ",
            "(c : Nat) => ",
            "Eq.trans MicroExpr ",
            "(micro_lift (MicroExpr.lam ty body) c Nat.zero) ",
            "(MicroExpr.lam ty (micro_lift body (Nat.succ c) Nat.zero)) ",
            "(MicroExpr.lam ty body) ",
            "(Eq.cong MicroExpr MicroExpr ",
            "(fun (x : MicroExpr) => MicroExpr.lam x (micro_lift body (Nat.succ c) Nat.zero)) ",
            "(micro_lift ty c Nat.zero) ty (ih_ty c)) ",
            "(Eq.cong MicroExpr MicroExpr ",
            "(fun (x : MicroExpr) => MicroExpr.lam ty x) ",
            "(micro_lift body (Nat.succ c) Nat.zero) body (ih_body (Nat.succ c)))) ",
            // pi branch (body recurses at Nat.succ c)
            "(fun (ty : MicroExpr) (body : MicroExpr) ",
            "(ih_ty : forall (c : Nat), Eq MicroExpr (micro_lift ty c Nat.zero) ty) ",
            "(ih_body : forall (c : Nat), Eq MicroExpr (micro_lift body c Nat.zero) body) ",
            "(c : Nat) => ",
            "Eq.trans MicroExpr ",
            "(micro_lift (MicroExpr.pi ty body) c Nat.zero) ",
            "(MicroExpr.pi ty (micro_lift body (Nat.succ c) Nat.zero)) ",
            "(MicroExpr.pi ty body) ",
            "(Eq.cong MicroExpr MicroExpr ",
            "(fun (x : MicroExpr) => MicroExpr.pi x (micro_lift body (Nat.succ c) Nat.zero)) ",
            "(micro_lift ty c Nat.zero) ty (ih_ty c)) ",
            "(Eq.cong MicroExpr MicroExpr ",
            "(fun (x : MicroExpr) => MicroExpr.pi ty x) ",
            "(micro_lift body (Nat.succ c) Nat.zero) body (ih_body (Nat.succ c)))) ",
            // let_ branch (ty, val recurse at c; body recurses at Nat.succ c)
            "(fun (ty : MicroExpr) (val : MicroExpr) (body : MicroExpr) ",
            "(ih_ty : forall (c : Nat), Eq MicroExpr (micro_lift ty c Nat.zero) ty) ",
            "(ih_val : forall (c : Nat), Eq MicroExpr (micro_lift val c Nat.zero) val) ",
            "(ih_body : forall (c : Nat), Eq MicroExpr (micro_lift body c Nat.zero) body) ",
            "(c : Nat) => ",
            "Eq.trans MicroExpr ",
            "(micro_lift (MicroExpr.let_ ty val body) c Nat.zero) ",
            "(MicroExpr.let_ ty (micro_lift val c Nat.zero) (micro_lift body (Nat.succ c) Nat.zero)) ",
            "(MicroExpr.let_ ty val body) ",
            "(Eq.cong MicroExpr MicroExpr ",
            "(fun (x : MicroExpr) => MicroExpr.let_ x (micro_lift val c Nat.zero) (micro_lift body (Nat.succ c) Nat.zero)) ",
            "(micro_lift ty c Nat.zero) ty (ih_ty c)) ",
            "(Eq.trans MicroExpr ",
            "(MicroExpr.let_ ty (micro_lift val c Nat.zero) (micro_lift body (Nat.succ c) Nat.zero)) ",
            "(MicroExpr.let_ ty val (micro_lift body (Nat.succ c) Nat.zero)) ",
            "(MicroExpr.let_ ty val body) ",
            "(Eq.cong MicroExpr MicroExpr ",
            "(fun (x : MicroExpr) => MicroExpr.let_ ty x (micro_lift body (Nat.succ c) Nat.zero)) ",
            "(micro_lift val c Nat.zero) val (ih_val c)) ",
            "(Eq.cong MicroExpr MicroExpr ",
            "(fun (x : MicroExpr) => MicroExpr.let_ ty val x) ",
            "(micro_lift body (Nat.succ c) Nat.zero) body (ih_body (Nat.succ c))))) ",
            // opaque_ branch
            "(fun (ty : MicroExpr) ",
            "(ih_ty : forall (c : Nat), Eq MicroExpr (micro_lift ty c Nat.zero) ty) ",
            "(c : Nat) => ",
            "Eq.cong MicroExpr MicroExpr MicroExpr.opaque_ ",
            "(micro_lift ty c Nat.zero) ty (ih_ty c)) ",
            // major premise + cutoff application
            "e c",
        )
        .to_string()
    }

    /// Proof term for `micro_level_eqb_symm`
    /// (`forall a b, micro_level_eqb a b = micro_level_eqb b a`).
    ///
    /// Double `MicroLevel.rec` (outer on `a` with a `b`-universalized motive,
    /// inner on `b`). Cross-constructor pairs both reduce to `Bool.false`
    /// (`Eq.refl Bool Bool.false`); `zero/zero` reduces to `Bool.true`; `succ`
    /// diagonal closes by the outer IH; the binary `max`/`imax` diagonals close
    /// by `Bool.and` congruence over the two outer IHs. Per-side, no
    /// commutativity of `Bool.and` is needed — the two normal forms are compared
    /// argument-wise. Part of the micro-band drain (Brick 4).
    fn micro_level_eqb_symm_value_src() -> String {
        // MicroLevel ctors: 0=zero, 1=succ, 2=max, 3=imax.
        // Inner minor-premise arm for ctor `ic` over inner-expr context `a`,
        // wrapping `body` (a term of the inner motive at that ctor). The ignored
        // recursive-field IH binders are annotated with the inner motive.
        fn arm(ic: usize, a: &str, body: &str) -> String {
            let im =
                |x: &str| format!("(Eq Bool (micro_level_eqb {a} {x}) (micro_level_eqb {x} {a}))");
            match ic {
                // `zero` is nullary: parenthesize the bare body so the outer
                // recursor treats it as ONE argument (not `Eq.refl`, `Bool`,
                // `Bool.true` as three separate recursor args).
                0 => format!("({body})"),
                1 => format!("(fun (bp : MicroLevel) (ihp : {}) => {body})", im("bp")),
                2 | 3 => format!(
                    "(fun (bl : MicroLevel) (br : MicroLevel) (ihl : {}) (ihr : {}) => {body})",
                    im("bl"),
                    im("br"),
                ),
                _ => unreachable!(),
            }
        }
        fn inner_rec(oc: usize, a: &str, diag: &str) -> String {
            let motive = format!(
                "(fun (b : MicroLevel) => Eq Bool (micro_level_eqb {a} b) (micro_level_eqb b {a}))"
            );
            let arms: Vec<String> = (0..4)
                .map(|ic| {
                    if ic == oc {
                        arm(ic, a, diag)
                    } else {
                        arm(ic, a, "Eq.refl Bool Bool.false")
                    }
                })
                .collect();
            format!(
                "(fun (b : MicroLevel) => MicroLevel.rec {} {} b)",
                motive,
                arms.join(" "),
            )
        }
        let outer_motive = "(fun (x : MicroLevel) => forall (b : MicroLevel), \
             Eq Bool (micro_level_eqb x b) (micro_level_eqb b x))";
        // zero: diagonal (inner zero) reduces to Bool.true on both sides.
        let outer_zero = inner_rec(0, "MicroLevel.zero", "Eq.refl Bool Bool.true");
        // succ ap: diagonal (inner succ) = ih_ap bp.
        let outer_succ = format!(
            "(fun (ap : MicroLevel) (ih_ap : forall (b : MicroLevel), \
              Eq Bool (micro_level_eqb ap b) (micro_level_eqb b ap)) => {})",
            inner_rec(1, "(MicroLevel.succ ap)", "ih_ap bp"),
        );
        // max/imax diagonal: Bool.and congruence over the two outer IHs.
        let diag_binary = "Eq.trans Bool \
             (Bool.and (micro_level_eqb al bl) (micro_level_eqb ar br)) \
             (Bool.and (micro_level_eqb bl al) (micro_level_eqb ar br)) \
             (Bool.and (micro_level_eqb bl al) (micro_level_eqb br ar)) \
             (Eq.cong Bool Bool (fun (z : Bool) => Bool.and z (micro_level_eqb ar br)) \
              (micro_level_eqb al bl) (micro_level_eqb bl al) (ih_al bl)) \
             (Eq.cong Bool Bool (fun (z : Bool) => Bool.and (micro_level_eqb bl al) z) \
              (micro_level_eqb ar br) (micro_level_eqb br ar) (ih_ar br))";
        let outer_binary = |ctor_expr: &str, oc: usize| {
            format!(
                "(fun (al : MicroLevel) (ar : MicroLevel) \
                  (ih_al : forall (b : MicroLevel), \
                   Eq Bool (micro_level_eqb al b) (micro_level_eqb b al)) \
                  (ih_ar : forall (b : MicroLevel), \
                   Eq Bool (micro_level_eqb ar b) (micro_level_eqb b ar)) => {})",
                inner_rec(oc, ctor_expr, diag_binary),
            )
        };
        let outer_max = outer_binary("(MicroLevel.max al ar)", 2);
        let outer_imax = outer_binary("(MicroLevel.imax al ar)", 3);
        format!(
            "fun (a : MicroLevel) => MicroLevel.rec {} {} {} {} {} a",
            outer_motive, outer_zero, outer_succ, outer_max, outer_imax,
        )
    }

    /// Proof term for `micro_structural_eq_symm`
    /// (`forall a b, micro_structural_eq a b = micro_structural_eq b a`).
    ///
    /// Double `MicroExpr.rec` (outer on `a` with a `b`-universalized motive,
    /// inner on `b`). All 42 cross-constructor pairs reduce to `Bool.false`
    /// (`Eq.refl Bool Bool.false`); the 7 diagonal arms close by: `bvar` →
    /// `nat_eqb_symm`; `sort` → `micro_level_eqb_symm`; `opaque_` → the single
    /// outer IH; `app`/`lam`/`pi` → `Bool.and` congruence over two outer IHs;
    /// `let_` → nested `Bool.and` congruence over three outer IHs. Per-side fuel
    /// means the two whnf normal forms are compared argument-wise, so no
    /// commutativity of `Bool.and` is required. Part of the micro-band drain
    /// (Brick 4).
    fn micro_structural_eq_symm_value_src() -> String {
        // MicroExpr ctors: 0=bvar, 1=sort, 2=app, 3=lam, 4=pi, 5=let_, 6=opaque_.
        fn arm(ic: usize, a: &str, body: &str) -> String {
            let im = |x: &str| {
                format!("(Eq Bool (micro_structural_eq {a} {x}) (micro_structural_eq {x} {a}))")
            };
            match ic {
                0 => format!("(fun (j : Nat) => {body})"),
                1 => format!("(fun (m : MicroLevel) => {body})"),
                2 => format!(
                    "(fun (g : MicroExpr) (c : MicroExpr) (ihg : {}) (ihc : {}) => {body})",
                    im("g"),
                    im("c"),
                ),
                3 => format!(
                    "(fun (t : MicroExpr) (d : MicroExpr) (iht : {}) (ihd : {}) => {body})",
                    im("t"),
                    im("d"),
                ),
                4 => format!(
                    "(fun (t : MicroExpr) (d : MicroExpr) (iht : {}) (ihd : {}) => {body})",
                    im("t"),
                    im("d"),
                ),
                5 => format!(
                    "(fun (t : MicroExpr) (v : MicroExpr) (d : MicroExpr) \
                      (iht : {}) (ihv : {}) (ihd : {}) => {body})",
                    im("t"),
                    im("v"),
                    im("d"),
                ),
                6 => format!("(fun (t : MicroExpr) (iht : {}) => {body})", im("t")),
                _ => unreachable!(),
            }
        }
        fn inner_rec(oc: usize, a: &str, diag: &str) -> String {
            let motive = format!(
                "(fun (b : MicroExpr) => \
                 Eq Bool (micro_structural_eq {a} b) (micro_structural_eq b {a}))"
            );
            let arms: Vec<String> = (0..7)
                .map(|ic| {
                    if ic == oc {
                        arm(ic, a, diag)
                    } else {
                        arm(ic, a, "Eq.refl Bool Bool.false")
                    }
                })
                .collect();
            format!(
                "(fun (b : MicroExpr) => MicroExpr.rec {} {} b)",
                motive,
                arms.join(" "),
            )
        }
        // Outer recursive-field IH binder for outer field `field`.
        let omih = |field: &str| {
            format!(
                "(ih_{field} : forall (b : MicroExpr), \
                 Eq Bool (micro_structural_eq {field} b) (micro_structural_eq b {field}))"
            )
        };
        let outer_motive = "(fun (x : MicroExpr) => forall (b : MicroExpr), \
             Eq Bool (micro_structural_eq x b) (micro_structural_eq b x))";
        // bvar / sort: non-recursive; diagonal via the *_symm substrate lemmas.
        let outer_bvar = format!(
            "(fun (i : Nat) => {})",
            inner_rec(0, "(MicroExpr.bvar i)", "nat_eqb_symm i j"),
        );
        let outer_sort = format!(
            "(fun (l : MicroLevel) => {})",
            inner_rec(1, "(MicroExpr.sort l)", "micro_level_eqb_symm l m"),
        );
        // app: Bool.and congruence over ih_f, ih_a1.
        let diag_app = "Eq.trans Bool \
             (Bool.and (micro_structural_eq f g) (micro_structural_eq a1 c)) \
             (Bool.and (micro_structural_eq g f) (micro_structural_eq a1 c)) \
             (Bool.and (micro_structural_eq g f) (micro_structural_eq c a1)) \
             (Eq.cong Bool Bool (fun (z : Bool) => Bool.and z (micro_structural_eq a1 c)) \
              (micro_structural_eq f g) (micro_structural_eq g f) (ih_f g)) \
             (Eq.cong Bool Bool (fun (z : Bool) => Bool.and (micro_structural_eq g f) z) \
              (micro_structural_eq a1 c) (micro_structural_eq c a1) (ih_a1 c))";
        let outer_app = format!(
            "(fun (f : MicroExpr) (a1 : MicroExpr) {} {} => {})",
            omih("f"),
            omih("a1"),
            inner_rec(2, "(MicroExpr.app f a1)", diag_app),
        );
        // lam: Bool.and congruence over ih_lty, ih_lb.
        let diag_lam = "Eq.trans Bool \
             (Bool.and (micro_structural_eq lty t) (micro_structural_eq lb d)) \
             (Bool.and (micro_structural_eq t lty) (micro_structural_eq lb d)) \
             (Bool.and (micro_structural_eq t lty) (micro_structural_eq d lb)) \
             (Eq.cong Bool Bool (fun (z : Bool) => Bool.and z (micro_structural_eq lb d)) \
              (micro_structural_eq lty t) (micro_structural_eq t lty) (ih_lty t)) \
             (Eq.cong Bool Bool (fun (z : Bool) => Bool.and (micro_structural_eq t lty) z) \
              (micro_structural_eq lb d) (micro_structural_eq d lb) (ih_lb d))";
        let outer_lam = format!(
            "(fun (lty : MicroExpr) (lb : MicroExpr) {} {} => {})",
            omih("lty"),
            omih("lb"),
            inner_rec(3, "(MicroExpr.lam lty lb)", diag_lam),
        );
        // pi: Bool.and congruence over ih_pty, ih_pb.
        let diag_pi = "Eq.trans Bool \
             (Bool.and (micro_structural_eq pty t) (micro_structural_eq pb d)) \
             (Bool.and (micro_structural_eq t pty) (micro_structural_eq pb d)) \
             (Bool.and (micro_structural_eq t pty) (micro_structural_eq d pb)) \
             (Eq.cong Bool Bool (fun (z : Bool) => Bool.and z (micro_structural_eq pb d)) \
              (micro_structural_eq pty t) (micro_structural_eq t pty) (ih_pty t)) \
             (Eq.cong Bool Bool (fun (z : Bool) => Bool.and (micro_structural_eq t pty) z) \
              (micro_structural_eq pb d) (micro_structural_eq d pb) (ih_pb d))";
        let outer_pi = format!(
            "(fun (pty : MicroExpr) (pb : MicroExpr) {} {} => {})",
            omih("pty"),
            omih("pb"),
            inner_rec(4, "(MicroExpr.pi pty pb)", diag_pi),
        );
        // let_: nested Bool.and congruence over ih_lety, ih_lev, ih_leb.
        let diag_let = "Eq.trans Bool \
             (Bool.and (micro_structural_eq lety t) \
              (Bool.and (micro_structural_eq lev v) (micro_structural_eq leb d))) \
             (Bool.and (micro_structural_eq t lety) \
              (Bool.and (micro_structural_eq lev v) (micro_structural_eq leb d))) \
             (Bool.and (micro_structural_eq t lety) \
              (Bool.and (micro_structural_eq v lev) (micro_structural_eq d leb))) \
             (Eq.cong Bool Bool \
              (fun (z : Bool) => Bool.and z \
               (Bool.and (micro_structural_eq lev v) (micro_structural_eq leb d))) \
              (micro_structural_eq lety t) (micro_structural_eq t lety) (ih_lety t)) \
             (Eq.trans Bool \
              (Bool.and (micro_structural_eq t lety) \
               (Bool.and (micro_structural_eq lev v) (micro_structural_eq leb d))) \
              (Bool.and (micro_structural_eq t lety) \
               (Bool.and (micro_structural_eq v lev) (micro_structural_eq leb d))) \
              (Bool.and (micro_structural_eq t lety) \
               (Bool.and (micro_structural_eq v lev) (micro_structural_eq d leb))) \
              (Eq.cong Bool Bool \
               (fun (z : Bool) => Bool.and (micro_structural_eq t lety) \
                (Bool.and z (micro_structural_eq leb d))) \
               (micro_structural_eq lev v) (micro_structural_eq v lev) (ih_lev v)) \
              (Eq.cong Bool Bool \
               (fun (z : Bool) => Bool.and (micro_structural_eq t lety) \
                (Bool.and (micro_structural_eq v lev) z)) \
               (micro_structural_eq leb d) (micro_structural_eq d leb) (ih_leb d)))";
        let outer_let = format!(
            "(fun (lety : MicroExpr) (lev : MicroExpr) (leb : MicroExpr) {} {} {} => {})",
            omih("lety"),
            omih("lev"),
            omih("leb"),
            inner_rec(5, "(MicroExpr.let_ lety lev leb)", diag_let),
        );
        // opaque_: single outer IH.
        let outer_opaque = format!(
            "(fun (oty : MicroExpr) {} => {})",
            omih("oty"),
            inner_rec(6, "(MicroExpr.opaque_ oty)", "ih_oty t"),
        );
        format!(
            "fun (a : MicroExpr) => MicroExpr.rec {} {} {} {} {} {} {} {} a",
            outer_motive,
            outer_bvar,
            outer_sort,
            outer_app,
            outer_lam,
            outer_pi,
            outer_let,
            outer_opaque,
        )
    }
}

#[cfg(test)]
mod micro_structural_eq_tests {
    use crate::spec::types::ProofStatus;
    use crate::spec::Specification;

    /// Build the implementation-soundness bundle, which includes
    /// `add_micro_checker` (and therefore the faithful `micro_structural_eq`
    /// stack registered by `add_micro_structural_eq`).
    fn build_micro_spec() -> Specification {
        Specification::new_implementation_soundness_test_spec()
            .expect("implementation-soundness spec (incl. micro_checker) should build")
    }

    /// `micro_structural_eq` is NO LONGER an axiom: it is a reducible
    /// Definition carrying a real recursive body, present in the kernel
    /// environment. This is the core anti-masquerade requirement: a faithful
    /// body replaced the bare `-> Bool` signature.
    #[test]
    fn test_micro_structural_eq_is_definition_not_axiom() {
        let spec = build_micro_spec();
        let def = spec
            .definitions()
            .get("micro_structural_eq")
            .expect("micro_structural_eq should be registered");
        assert!(
            !def.is_axiom,
            "micro_structural_eq must no longer be an axiom (it has a faithful body)"
        );
        assert!(
            spec.env()
                .get_const(&clean_kernel::Name::from_string("micro_structural_eq"))
                .is_some(),
            "micro_structural_eq should be in the kernel environment"
        );
        // The level-equality substrate is registered too.
        assert!(
            spec.env()
                .get_const(&clean_kernel::Name::from_string("micro_level_eqb"))
                .is_some(),
            "micro_level_eqb should be in the kernel environment"
        );
    }

    /// The reflexivity metatheorem and its supporting lemmas are DerivedProved
    /// with an empty (foundational) axiom closure — genuine kernel-checked
    /// proofs, zero domain axioms.
    #[test]
    fn test_micro_structural_eq_refl_chain_proved_foundational() {
        let spec = build_micro_spec();
        let defs = spec.definitions();
        for name in [
            "micro_nat_eqb_refl",
            "micro_level_eqb_refl",
            "micro_structural_eq_refl",
        ] {
            let def = defs
                .get(name)
                .unwrap_or_else(|| panic!("lemma {name} should be registered"));
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "lemma {name} must be DerivedProved (constructive proof)"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "lemma {name} must have empty axiom closure (foundational), got {:?}",
                def.axiom_deps
            );
            assert!(!def.is_axiom, "lemma {name} must not be an axiom");
        }

        // The deliverable literally states the reflexivity property and carries
        // a kernel-checked proof term (registered as a Theorem).
        let refl = defs
            .get("micro_structural_eq_refl")
            .expect("micro_structural_eq_refl should be registered");
        assert!(
            refl.type_src.contains("micro_structural_eq e e")
                && refl.type_src.contains("Bool.true"),
            "micro_structural_eq_refl must literally state micro_structural_eq e e = true, got: {}",
            refl.type_src
        );
        let decl = spec
            .env()
            .get_const(&clean_kernel::Name::from_string("micro_structural_eq_refl"))
            .expect("micro_structural_eq_refl should be in the kernel environment");
        assert_eq!(
            decl.kind,
            clean_kernel::ConstantKind::Theorem,
            "micro_structural_eq_refl should be a kernel Theorem"
        );
        assert!(
            decl.value.is_some(),
            "micro_structural_eq_refl Theorem should carry its proof value"
        );
    }

    /// Non-vacuity / masquerade guard: `micro_structural_eq` is a GENUINE
    /// structural equality, not constantly-true. The three `*_false` witnesses
    /// only kernel-checked (i.e. `build_micro_spec` only succeeded) because
    /// `micro_structural_eq` actually reduces to `false` on distinct
    /// expressions:
    ///   - distinct constructors (sort vs bvar; app vs lam)
    ///   - same constructor, distinct payload (bvar 0 vs bvar 1)
    #[test]
    fn test_micro_structural_eq_non_vacuous_false_on_distinct() {
        let spec = build_micro_spec();
        let defs = spec.definitions();
        for name in [
            "micro_structural_eq_distinct_sort_bvar_false",
            "micro_structural_eq_distinct_app_lam_false",
            "micro_structural_eq_distinct_bvar_index_false",
        ] {
            let def = defs
                .get(name)
                .unwrap_or_else(|| panic!("non-vacuity witness {name} should be registered"));
            assert!(
                def.type_src.contains("Bool.false"),
                "witness {name} must assert the result is false"
            );
            assert_eq!(
                def.proof_status,
                ProofStatus::DerivedProved,
                "witness {name} must be DerivedProved"
            );
            // The witness is in the kernel env => its Eq.refl Bool false proof
            // kernel-checked => micro_structural_eq genuinely reduced the
            // distinct pair to false. This is the masquerade guard.
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(name))
                    .is_some(),
                "witness {name} should be in the kernel environment (proof checked)"
            );
        }
    }
}

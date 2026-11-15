// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Foundation types: Eq, ProdType, Nat, Bool, AndType (PARTs 1, 1.5, 2, 3, 3.5)

use std::collections::HashSet;

use crate::proofs::builder::ProofBuilder;
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::model_units::ModelUnit;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;
use clean_kernel::{Expr, Level};

impl Specification {
    pub(crate) fn nat_sub_zero_left_value_expr() -> Expr {
        fn level_one() -> Level {
            Level::succ(Level::zero())
        }

        fn eq_const() -> Expr {
            Expr::const_str_levels("Eq", vec![level_one()])
        }

        fn eq_refl_const() -> Expr {
            Expr::const_str_levels("Eq.refl", vec![level_one()])
        }

        fn eq_cong_const() -> Expr {
            Expr::const_str_levels("Eq.cong", vec![level_one(), level_one()])
        }

        fn eq_trans_const() -> Expr {
            Expr::const_str_levels("Eq.trans", vec![level_one()])
        }

        fn nat_rec_const() -> Expr {
            Expr::const_str_levels("Nat.rec", vec![Level::zero()])
        }

        fn nat_expr() -> Expr {
            Expr::const_str("Nat")
        }

        fn nat_zero() -> Expr {
            Expr::const_str("Nat.zero")
        }

        fn nat_succ(arg: Expr) -> Expr {
            Expr::app(Expr::const_str("Nat.succ"), arg)
        }

        fn nat_pred(arg: Expr) -> Expr {
            Expr::app(Expr::const_str("Nat.pred"), arg)
        }

        fn nat_sub(lhs: Expr, rhs: Expr) -> Expr {
            Expr::apps(Expr::const_str("Nat.sub"), [lhs, rhs])
        }

        fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
            Expr::apps(eq_const(), [nat_expr(), lhs, rhs])
        }

        fn eq_refl_nat(value: Expr) -> Expr {
            Expr::apps(eq_refl_const(), [nat_expr(), value])
        }

        fn eq_cong_nat(f: Expr, lhs: Expr, rhs: Expr, proof: Expr) -> Expr {
            Expr::apps(
                eq_cong_const(),
                [nat_expr(), nat_expr(), f, lhs, rhs, proof],
            )
        }

        fn eq_trans_nat(a: Expr, b: Expr, c: Expr, ab: Expr, bc: Expr) -> Expr {
            Expr::apps(eq_trans_const(), [nat_expr(), a, b, c, ab, bc])
        }

        let mut b = ProofBuilder::new();
        let nat = nat_expr();
        b.lam("n", nat.clone(), |b| {
            let motive = b.lam("k", nat.clone(), |b| {
                eq_nat(nat_sub(nat_zero(), b.var("k")), nat_zero())
            });
            let zero_case = eq_refl_nat(nat_zero());
            let step_case = b.lam("k", nat.clone(), |b| {
                let ih_ty = eq_nat(nat_sub(nat_zero(), b.var("k")), nat_zero());
                b.lam("ih", ih_ty, |b| {
                    let h_pred = eq_cong_nat(
                        Expr::const_str("Nat.pred"),
                        nat_sub(nat_zero(), b.var("k")),
                        nat_zero(),
                        b.var("ih"),
                    );
                    eq_trans_nat(
                        nat_sub(nat_zero(), nat_succ(b.var("k"))),
                        nat_pred(nat_zero()),
                        nat_zero(),
                        h_pred,
                        eq_refl_nat(nat_zero()),
                    )
                })
            });
            Expr::apps(nat_rec_const(), [motive, zero_case, step_case, b.var("n")])
        })
    }

    pub(crate) fn nat_sub_succ_succ_value_expr() -> Expr {
        fn level_one() -> Level {
            Level::succ(Level::zero())
        }

        fn eq_const() -> Expr {
            Expr::const_str_levels("Eq", vec![level_one()])
        }

        fn eq_refl_const() -> Expr {
            Expr::const_str_levels("Eq.refl", vec![level_one()])
        }

        fn eq_cong_const() -> Expr {
            Expr::const_str_levels("Eq.cong", vec![level_one(), level_one()])
        }

        fn nat_rec_const() -> Expr {
            Expr::const_str_levels("Nat.rec", vec![Level::zero()])
        }

        fn nat_expr() -> Expr {
            Expr::const_str("Nat")
        }

        fn nat_succ(arg: Expr) -> Expr {
            Expr::app(Expr::const_str("Nat.succ"), arg)
        }

        fn nat_sub(lhs: Expr, rhs: Expr) -> Expr {
            Expr::apps(Expr::const_str("Nat.sub"), [lhs, rhs])
        }

        fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
            Expr::apps(eq_const(), [nat_expr(), lhs, rhs])
        }

        fn eq_refl_nat(value: Expr) -> Expr {
            Expr::apps(eq_refl_const(), [nat_expr(), value])
        }

        fn eq_cong_nat(f: Expr, lhs: Expr, rhs: Expr, proof: Expr) -> Expr {
            Expr::apps(
                eq_cong_const(),
                [nat_expr(), nat_expr(), f, lhs, rhs, proof],
            )
        }

        let mut b = ProofBuilder::new();
        let nat = nat_expr();
        b.lam("a", nat.clone(), |b| {
            b.lam("b", nat.clone(), |b| {
                let motive = b.lam("k", nat.clone(), |b| {
                    eq_nat(
                        nat_sub(nat_succ(b.var("a")), nat_succ(b.var("k"))),
                        nat_sub(b.var("a"), b.var("k")),
                    )
                });
                let zero_case = eq_refl_nat(b.var("a"));
                let step_case = b.lam("k", nat.clone(), |b| {
                    let ih_ty = eq_nat(
                        nat_sub(nat_succ(b.var("a")), nat_succ(b.var("k"))),
                        nat_sub(b.var("a"), b.var("k")),
                    );
                    b.lam("ih", ih_ty, |b| {
                        eq_cong_nat(
                            Expr::const_str("Nat.pred"),
                            nat_sub(nat_succ(b.var("a")), nat_succ(b.var("k"))),
                            nat_sub(b.var("a"), b.var("k")),
                            b.var("ih"),
                        )
                    })
                });
                Expr::apps(nat_rec_const(), [motive, zero_case, step_case, b.var("b")])
            })
        })
    }

    fn add_foundation_equality(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 1: Equality type (Eq, rfl)
        // =========================================================
        // The Eq type is the propositional equality type from Lean 4.
        // Eq : {α : Sort u} → α → α → Prop
        // Constructor: rfl : Eq a a

        // Eq inductive type
        self.register_model_unit(ModelUnit::FoundationEq)?;

        // Eq.symm: symmetry of equality — PROVED from Eq.rec (based Martin-Löf J).
        // Based path induction on h at the base point a: motive M b _ := Eq α b a,
        // refl minor M a (Eq.refl α a) = Eq α a a discharged by Eq.refl α a, so
        // Eq.rec α a M (Eq.refl α a) b h : Eq α b a. Zero axiom_deps (Eq / Eq.rec /
        // Eq.refl are non-axiom kernel declarations). Foundational-consequence lemma:
        // provable all along — was a value-less FoundationalRule axiom.
        self.add_definition_checked(SpecDefinition {
            name: "Eq.symm".to_string(),
            type_src: "forall (α : Sort u) (a : α) (b : α), Eq α a b -> Eq α b a".to_string(),
            value_src: Some(
                "fun (α : Sort u) (a : α) (b : α) (h : Eq α a b) => \
                 @Eq.rec α a (fun (b1 : α) (_h : Eq α a b1) => Eq α b1 a) \
                 (@Eq.refl α a) b h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Symmetry of equality: if a = b then b = a. PROVED via based Eq.rec \
                          (Martin-Löf J): motive (fun b1 _ => Eq α b1 a), refl minor Eq.refl α a. \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Eq.trans: transitivity of equality — PROVED from Eq.rec (based J) directly
        // (no dependency on Eq.subst, which is registered later in this stage).
        // Based path induction on hbc at base point b: motive M x _ := Eq α a x,
        // refl minor M b (Eq.refl α b) = Eq α a b discharged by hab, so
        // Eq.rec α b M hab c hbc : Eq α a c. Zero axiom_deps.
        self.add_definition_checked(SpecDefinition {
            name: "Eq.trans".to_string(),
            type_src:
                "forall (α : Sort u) (a : α) (b : α) (c : α), Eq α a b -> Eq α b c -> Eq α a c"
                    .to_string(),
            value_src: Some(
                "fun (α : Sort u) (a : α) (b : α) (c : α) (hab : Eq α a b) (hbc : Eq α b c) => \
                 @Eq.rec α b (fun (x : α) (_h : Eq α b x) => Eq α a x) hab c hbc"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Transitivity of equality: if a = b and b = c then a = c. PROVED via \
                          based Eq.rec (Martin-Löf J) on hbc: motive (fun x _ => Eq α a x), refl \
                          minor hab. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["Eq".to_string(), "Eq.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // Eq.cong: congruence of equality — PROVED from Eq.rec (based J).
        // Based path induction on h at base point a: motive M x _ := Eq β (f a) (f x),
        // refl minor M a (Eq.refl α a) = Eq β (f a) (f a) discharged by Eq.refl β (f a),
        // so Eq.rec α a M (Eq.refl β (f a)) b h : Eq β (f a) (f b). Zero axiom_deps.
        self.add_definition_checked(SpecDefinition {
            name: "Eq.cong".to_string(),
            type_src: "forall (α : Sort u) (β : Sort v) (f : α -> β) (a : α) (b : α), Eq α a b -> Eq β (f a) (f b)".to_string(),
            value_src: Some(
                "fun (α : Sort u) (β : Sort v) (f : α -> β) (a : α) (b : α) (h : Eq α a b) => \
                 @Eq.rec α a (fun (x : α) (_h : Eq α a x) => Eq β (f a) (f x)) \
                 (@Eq.refl β (f a)) b h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Congruence: if a = b then f(a) = f(b). PROVED via based Eq.rec \
                          (Martin-Löf J): motive (fun x _ => Eq β (f a) (f x)), refl minor \
                          Eq.refl β (f a). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq".to_string(),
                "Eq.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Eq.subst: substitution of equals.
        // The motive lands in `Prop` (`P : α -> Prop`), MATCHING the canonical
        // Lean / kernel `Eq.subst` (core_eq/transport.rs: `motive : α -> Prop`,
        // one universe `Eq.subst.{u}`). The previous `P : α -> Type` (Sort 1)
        // diverged from the kernel and REJECTED the Prop motive the kernel's own
        // Int/Rat proofs supply — e.g. `Int.le_refl` transports along
        // `@Eq.subst.{1} Int (fun x => Int.NonNeg x)` (motive `Int -> Prop`),
        // which failed "expected Sort 1, got Sort 0" once `init_rat`'s idempotent
        // `init_eq` kept this foundation `Eq.subst` instead of registering the
        // kernel one. Every foundation consumer site already passes a Prop motive
        // (`fun x => Typing x …` / `fun x => DefEq x …`), so `Prop` breaks none
        // and keeps the single universe (no `Eq.subst.{1}` arity change).
        // PROVED from Eq.rec (based J). Based path induction on h at base point a:
        // direct transport motive M x _ := P x (the based form supplies the refl
        // minor at the base point where P a is already in hand), refl minor pa : P a,
        // so Eq.rec α a M pa b h : P b. Motive lands in Prop (P : α -> Prop). Zero
        // axiom_deps.
        self.add_definition_checked(SpecDefinition {
            name: "Eq.subst".to_string(),
            type_src: "forall (α : Sort u) (P : α -> Prop) (a : α) (b : α), Eq α a b -> P a -> P b"
                .to_string(),
            value_src: Some(
                "fun (α : Sort u) (P : α -> Prop) (a : α) (b : α) (h : Eq α a b) (pa : P a) => \
                 @Eq.rec α a (fun (x : α) (_h : Eq α a x) => P x) pa b h"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Substitution: if a = b and P(a), then P(b). PROVED via based Eq.rec \
                          (Martin-Löf J): transport motive (fun x _ => P x), refl minor pa. \
                          Prop motive. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["Eq".to_string(), "Eq.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // Eq.substType: universe-POLYMORPHIC substitution (`P : α -> Sort w`),
        // the foundation's canonical Leibniz transport. The self-verification
        // surface substitutes along `Eq` into motives that land in TYPE (Sort 1)
        // — `Typing : KExpr -> KExpr -> Type` and `DefEq` are in Type, and the
        // KExpr constructor-discrimination lemmas use a Type-valued discriminator
        // (`KExpr.rec` to `Nat`/`Empty`) — as well as motives in Prop. `Sort w`
        // admits every one (w=0 Prop, w=1 Type, …). It is split from `Eq.subst`,
        // which is held at the canonical kernel shape (`P : α -> Prop`, one
        // universe `Eq.subst.{u}`, matching core_eq/transport.rs) so the kernel's
        // OWN Int/Rat proofs — which reference `@Eq.subst.{1}` with a Prop motive
        // — type-check against this foundation surface when `init_rat`'s
        // idempotent `init_eq` keeps the foundation `Eq.subst`. Every clean-verify
        // transport uses `Eq.substType`; only the kernel proofs use `Eq.subst`.
        // PROVED from Eq.rec (based J) — the SAME transport proof as Eq.subst, only
        // the motive lands in `Sort w` (large elimination). The generated Eq.rec
        // carries a SEPARATE motive universe param (u_1), so it supports elimination
        // into any Sort w (w=0 Prop, w=1 Type, …) — Eq is a subsingleton, so the
        // kernel's recursor is large-eliminating. Zero axiom_deps.
        self.add_definition_checked(SpecDefinition {
            name: "Eq.substType".to_string(),
            type_src:
                "forall (α : Sort u) (P : α -> Sort w) (a : α) (b : α), Eq α a b -> P a -> P b"
                    .to_string(),
            value_src: Some(
                "fun (α : Sort u) (P : α -> Sort w) (a : α) (b : α) (h : Eq α a b) (pa : P a) => \
                 @Eq.rec α a (fun (x : α) (_h : Eq α a x) => P x) pa b h"
                    .to_string(),
            ),
            is_axiom: false,
            description:
                "Large-elimination substitution (Type motive): if a = b and P(a), then P(b). \
                 PROVED via based Eq.rec (Martin-Löf J) with a Sort w motive (fun x _ => P x); \
                 Eq's recursor is large-eliminating (subsingleton). Zero axiom_deps."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["Eq".to_string(), "Eq.rec".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    pub(super) fn add_foundation_types(&mut self) -> Result<(), SpecError> {
        self.add_foundation_equality()?;

        // =========================================================
        // PART 1.5: Product Types
        // =========================================================
        // ProdType, AndType, and basic structural types needed for proof terms.

        // ProdType type (pair/product)
        self.register_model_unit(ModelUnit::FoundationProd)?;

        // ProdType.mk constructor and ProdType.rec recursor are auto-registered by add_inductive.

        // ProdType.fst / .snd projectors + .fst_beta / .snd_beta computation rules.
        //
        // Previously FOUR FoundationalRule hand axioms: the two value-less
        // projectors and the two value-less β/computation rules. `ProdType` is a
        // genuine `add_inductive` (single constructor `mk : α → β → ProdType α β`,
        // above) whose auto-generated recursor `ProdType.rec` (is_axiom:false,
        // uncounted) makes both projections genuine kernel-checked terms and both
        // computation rules genuine Eq.refl proofs — NOT new assumptions. This is
        // the AndType.left/.right drain pattern applied to ProdType, and closes the
        // FAMILY 4 slice of the inductive-encoding drain (after DefEq / Typing /
        // TypedDefEq / DefinitionalExtension). ZERO new axioms.

        // ProdType.fst: PROVED via the single-constructor recursor with motive
        // (fun _ => α) and minor premise (fun a b => a). Beta-only typing; closure
        // reaches only ProdType / ProdType.rec, so the kernel-ground-truth axiom_deps
        // is EMPTY. Registered REDUCIBLE (add_definition_reducible → a semireducible
        // Declaration::Definition, not the Opaque form add_definition gives non-Prop
        // valued defs) so the kernel unfolds fst during defeq — required for the
        // ProdType.fst_beta Eq.refl proof to iota-reduce fst (mk a b) to a. This is a
        // one-step recursor projection, so the #1385 expensive/infinite-reduction
        // concern does not apply (same rationale as the type-level reducible aliases).
        self.add_definition_reducible(SpecDefinition {
            name: "ProdType.fst".to_string(),
            type_src: "forall (α : Type) (β : Type), ProdType α β -> α".to_string(),
            value_src: Some(
                "fun (α : Type) (β : Type) (p : ProdType α β) => \
                 @ProdType.rec α β (fun (_p : ProdType α β) => α) \
                 (fun (a : α) (b : β) => a) p"
                    .to_string(),
            ),
            is_axiom: false,
            description: "First projection. PROVED via ProdType.rec: the single-constructor \
                          recursor with motive (fun _ => α) and minor premise (fun a b => a). \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ProdType".to_string(),
                "ProdType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ProdType.snd: drained identically to ProdType.fst (motive (fun _ => β),
        // minor premise (fun a b => b)). REDUCIBLE for the same reason (snd_beta).
        self.add_definition_reducible(SpecDefinition {
            name: "ProdType.snd".to_string(),
            type_src: "forall (α : Type) (β : Type), ProdType α β -> β".to_string(),
            value_src: Some(
                "fun (α : Type) (β : Type) (p : ProdType α β) => \
                 @ProdType.rec α β (fun (_p : ProdType α β) => β) \
                 (fun (a : α) (b : β) => b) p"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Second projection. PROVED via ProdType.rec: the single-constructor \
                          recursor with motive (fun _ => β) and minor premise (fun a b => b). \
                          Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ProdType".to_string(),
                "ProdType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ProdType.fst_beta: computation rule for fst — now PROVED by Eq.refl. With
        // ProdType.fst a genuine recursor definition, ProdType.fst α β (mk α β a b)
        // delta-unfolds then iota-reduces (ProdType.rec on mk) to a, so the two
        // sides are definitionally equal and Eq.refl α a checks. Zero axiom_deps.
        self.add_definition(SpecDefinition {
            name: "ProdType.fst_beta".to_string(),
            type_src: "forall (α : Type) (β : Type) (a : α) (b : β), Eq α (ProdType.fst α β (@ProdType.mk α β a b)) a".to_string(),
            value_src: Some(
                "fun (α : Type) (β : Type) (a : α) (b : β) => @Eq.refl α a".to_string(),
            ),
            is_axiom: false,
            description: "fst (mk a b) = a. PROVED via Eq.refl: ProdType.fst iota-reduces on \
                          ProdType.mk to the first field. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ProdType.fst".to_string(),
                "ProdType.mk".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // ProdType.snd_beta: computation rule for snd — drained identically to
        // fst_beta via Eq.refl (ProdType.snd iota-reduces on mk to the second field).
        self.add_definition(SpecDefinition {
            name: "ProdType.snd_beta".to_string(),
            type_src: "forall (α : Type) (β : Type) (a : α) (b : β), Eq β (ProdType.snd α β (@ProdType.mk α β a b)) b".to_string(),
            value_src: Some(
                "fun (α : Type) (β : Type) (a : α) (b : β) => @Eq.refl β b".to_string(),
            ),
            is_axiom: false,
            description: "snd (mk a b) = b. PROVED via Eq.refl: ProdType.snd iota-reduces on \
                          ProdType.mk to the second field. Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "ProdType.snd".to_string(),
                "ProdType.mk".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // PART 2: Natural Numbers
        // =========================================================
        // Nat type is used for universe levels, de Bruijn indices, etc.

        // Nat inductive type
        self.register_model_unit(ModelUnit::FoundationNat)?;

        // nat_add_zero: 0 + n = n
        // Derived using Nat.rec: match on m with zero -> refl, succ m' -> cong succ IH
        // Uses structural registration because the Nat.rec motive application
        // involves iota reductions the kernel's defEq checker cannot reduce.
        self.add_definition_structural(SpecDefinition {
            name: "nat_add_zero".to_string(),
            type_src: "forall (n : Nat), Eq Nat (Nat.add Nat.zero n) n".to_string(),
            value_src: Some(
                "fun (n : Nat) => @Nat.rec (fun (m : Nat) => Eq Nat (Nat.add Nat.zero m) m) (@Eq.refl Nat Nat.zero) (fun (m : Nat) (ih : Eq Nat (Nat.add Nat.zero m) m) => Eq.cong Nat Nat Nat.succ (Nat.add Nat.zero m) m ih) n"
                    .to_string(),
            ),
            is_axiom: false,
            description: "0 + n = n, by induction.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.cong".to_string(),
            ])),
            // Eq.cong, Eq.refl, Nat.rec are all FoundationalRules — no axiom deps.
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_succ_succ: Nat.sub (succ a) (succ b) = Nat.sub a b
        // Nat.sub recurses on b through Nat.pred, so the symbolic successor
        // case needs induction on b rather than plain Eq.refl.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_succ_succ".to_string(),
            type_src: "forall (a : Nat) (b : Nat), Eq Nat (Nat.sub (Nat.succ a) (Nat.succ b)) (Nat.sub a b)".to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) (b : Nat) => @Nat.rec ",
                "(fun (k : Nat) => Eq Nat (Nat.sub (Nat.succ a) (Nat.succ k)) (Nat.sub a k)) ",
                "(@Eq.refl Nat a) ",
                "(fun (k : Nat) (ih : Eq Nat (Nat.sub (Nat.succ a) (Nat.succ k)) (Nat.sub a k)) => ",
                "Eq.cong Nat Nat Nat.pred ",
                "(Nat.sub (Nat.succ a) (Nat.succ k)) ",
                "(Nat.sub a k) ",
                "ih) ",
                "b",
            )
            .to_string()),
            is_axiom: false,
            description: "Nat.sub (succ a) (succ b) = Nat.sub a b. DerivedProved via Nat.rec on b and Eq.cong Nat.pred. Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: Some(Self::nat_sub_succ_succ_value_expr()),
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Nat.pred".to_string(),
                "Eq.refl".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // nat_sub_self: n - n = 0
        // Derived by Nat.rec induction using nat_sub_succ_succ transport.
        // Base: Nat.sub 0 0 = 0 by Eq.refl (match on zero → zero).
        // Step: Eq.trans (nat_sub_succ_succ n n) ih chains
        //   Nat.sub (succ n) (succ n) = Nat.sub n n = 0.
        // Part of #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "nat_sub_self".to_string(),
            type_src: "forall (a : Nat), Eq Nat (Nat.sub a a) Nat.zero".to_string(),
            value_src: Some(concat!(
                "fun (a : Nat) => @Nat.rec ",
                "(fun (n : Nat) => Eq Nat (Nat.sub n n) Nat.zero) ",
                "(@Eq.refl Nat Nat.zero) ",
                "(fun (n : Nat) (ih : Eq Nat (Nat.sub n n) Nat.zero) => ",
                "Eq.trans Nat ",
                "(Nat.sub (Nat.succ n) (Nat.succ n)) ",
                "(Nat.sub n n) ",
                "Nat.zero ",
                "(nat_sub_succ_succ n n) ",
                "ih) ",
                "a",
            ).to_string()),
            is_axiom: false,
            description: "n - n = 0, by Nat.rec induction + nat_sub_succ_succ transport. DerivedProved. Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Nat.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "nat_sub_succ_succ".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Lt: strict less-than on naturals
        self.register_model_unit(ModelUnit::FoundationOrder)?;

        // =========================================================
        // PART 3: Boolean type
        // =========================================================
        // Bool is used for decidable equality and computational checks.

        // Bool inductive type — register the KERNEL's `Bool` (env.init_bool)
        // rather than an elaborator-built one. The kernel's `Bool` carries the
        // recursor that the kernel's own BoolAnalysis corpus (`Bool.beq`,
        // `BoolAnalysis.ind`, the `disagree_sq_*` bridges) reduces against; an
        // elaborator-generated `Bool` does not fire the same iota reduction, so
        // those proofs get stuck in def-eq. Idempotent: init_boolean_analysis's
        // later `init_bool` sees `bool_init` and skips. The foundation's own
        // reducing `Bool.not`/`and`/`or` (below) bind to this kernel `Bool.rec`.
        self.env_mut()
            .init_bool()
            .map_err(|e| SpecError::EnvError(e.to_string()))?;
        // `Bool.not` / `Bool.and` / `Bool.or` are provided by the kernel
        // `init_bool` surface (`register_bool_surface`) as the same `Bool.rec`-
        // based reducing definitions the foundation used; re-registering them
        // here would be a duplicate `add_decl`, so they are intentionally not
        // redeclared.

        // =========================================================
        // PART 3.25: Empty type (no constructors)
        // =========================================================
        // Empty is the uninhabited type in Type. Used for constructor
        // discrimination via large elimination (KExpr.rec with Type-valued
        // motive). Empty.rec : (motive : Empty -> Sort u) -> (t : Empty) -> motive t.
        // Part of #464: Phase 4A constructive derivation.

        self.register_model_unit(ModelUnit::FoundationEmptyAnd)?;
        // The agreement equations reference Nat/Nat.add/Nat.pred/Nat.sub, Eq, Empty
        // and the kernel's Bool, so they register AFTER all of them. They are in the
        // LIVE spec so the independent Lean replay re-checks them: the exporter roots
        // at registered spec definitions, so a unit outside the spec is invisible to
        // Lean. The same text is decided over the compiler prelude as an island.
        self.register_model_unit(ModelUnit::FoundationAgreement)?;

        // AndType.left: extract left conjunct.
        //
        // DRAINED (census 139→…): formerly a value-less FoundationalRule axiom
        // (a hand-declared projector). `AndType` is a real `add_inductive` whose
        // auto-generated recursor `AndType.rec` (is_axiom:false, uncounted) makes
        // the projection a genuine kernel-checked term — NOT a new assumption.
        // The IDENTICAL projection already type-checks inside the live
        // DerivedProved `par_reduces_p_spine_cong_below_boundary_proof`
        // (complete_development.rs ~:3992). Beta-only typing; closure reaches
        // only `AndType` / `AndType.rec`, so the kernel-ground-truth axiom_deps
        // is EMPTY (zero new trust).
        self.add_definition(SpecDefinition {
            name: "AndType.left".to_string(),
            type_src: "forall (A : Type) (B : Type), AndType A B -> A".to_string(),
            value_src: Some(
                "fun (A : Type) (B : Type) (p : AndType A B) => \
                 @AndType.rec A B (fun (_p : AndType A B) => A) \
                 (fun (a : A) (b : B) => a) p"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Extract left conjunct from AndType. PROVED via AndType.rec: \
                          the single-constructor recursor with motive (fun _ => A) and \
                          minor premise (fun a b => a). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "AndType".to_string(),
                "AndType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // AndType.right: extract right conjunct. Drained identically to
        // `AndType.left` (motive (fun _ => B), minor premise (fun a b => b)).
        self.add_definition(SpecDefinition {
            name: "AndType.right".to_string(),
            type_src: "forall (A : Type) (B : Type), AndType A B -> B".to_string(),
            value_src: Some(
                "fun (A : Type) (B : Type) (p : AndType A B) => \
                 @AndType.rec A B (fun (_p : AndType A B) => B) \
                 (fun (a : A) (b : B) => b) p"
                    .to_string(),
            ),
            is_axiom: false,
            description: "Extract right conjunct from AndType. PROVED via AndType.rec: \
                          the single-constructor recursor with motive (fun _ => B) and \
                          minor premise (fun a b => b). Zero axiom_deps."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "AndType".to_string(),
                "AndType.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::build_spec_with_stack;

    #[test]
    fn test_le_registers_inductive_constructor_surface() {
        let spec = build_spec_with_stack();
        for name in ["Le", "Le.refl", "Le.step", "Le.rec"] {
            assert!(
                spec.definitions().contains_key(name),
                "full core spec should register {name}"
            );
        }
    }
}

#[cfg(test)]
mod equality_helpers_tests {
    use super::*;

    #[test]
    fn equality_helpers_register_and_recheck_without_axioms() {
        let mut spec = Specification::new_empty();
        spec.add_foundation_equality()
            .expect("the unchanged equality model and all five helper proofs register");
        for name in ["Eq.symm", "Eq.trans", "Eq.cong", "Eq.subst", "Eq.substType"] {
            let definition = spec.get_definition(name).expect("registered helper");
            assert!(!definition.is_axiom, "{name} must carry a proof value");
            assert!(
                definition.axiom_deps.is_empty(),
                "{name} has axiom dependencies"
            );
            let value = definition
                .elaborated_value
                .as_ref()
                .expect("actual proof term");
            let type_ = definition
                .elaborated_type
                .as_ref()
                .expect("actual statement");
            clean_kernel::TypeChecker::new(spec.env())
                .check_type(value, type_)
                .unwrap_or_else(|error| panic!("{name} fails a fresh kernel check: {error}"));
        }
    }
}

#[cfg(test)]
mod projection_tests {
    use super::*;
    use clean_kernel::{Name, TypeChecker};

    #[test]
    fn foundation_projections_recheck_without_axioms_and_compute_both_fields() {
        crate::test_utils::run_with_stack(|| {
            for source in [
                crate::spec::model_units::ModelUnitSource::CleanFiles,
                crate::spec::model_units::ModelUnitSource::RetainedLiterals,
            ] {
                let mut spec = Specification::new_empty();
                spec.set_model_unit_source(source);
                spec.add_foundation_types()
                    .expect("real foundation initializer");
                for name in [
                    "ProdType.fst",
                    "ProdType.snd",
                    "ProdType.fst_beta",
                    "ProdType.snd_beta",
                    "AndType.left",
                    "AndType.right",
                ] {
                    let definition = spec.get_definition(name).expect("registered projection");
                    let value = definition.elaborated_value.as_ref().expect("actual value");
                    let ty = definition.elaborated_type.as_ref().expect("actual type");
                    TypeChecker::new(spec.env())
                        .check_type(value, ty)
                        .unwrap_or_else(|error| panic!("{name} fails fresh kernel check: {error}"));
                    let root = Name::from_string(name);
                    assert!(
                        spec.env()
                            .axiom_deps(&root)
                            .expect("root exists")
                            .is_empty(),
                        "{name} has axioms"
                    );
                    assert!(
                        spec.env()
                            .trust_marker_deps(&root)
                            .expect("root exists")
                            .is_empty(),
                        "{name} has trust markers"
                    );
                }
                let nat = Expr::const_str("Nat");
                let bool_ = Expr::const_str("Bool");
                let two = Expr::nat_lit(2);
                let false_ = Expr::const_str("Bool.false");
                let pair = Expr::apps(
                    Expr::const_str("ProdType.mk"),
                    [nat.clone(), bool_.clone(), two.clone(), false_.clone()],
                );
                let first = Expr::apps(
                    Expr::const_str("ProdType.fst"),
                    [nat.clone(), bool_.clone(), pair.clone()],
                );
                let second = Expr::apps(Expr::const_str("ProdType.snd"), [nat, bool_, pair]);
                let tc = TypeChecker::new(spec.env());
                assert!(tc.is_def_eq(&first, &two));
                assert!(!tc.is_def_eq(&first, &Expr::nat_lit(3)));
                assert!(tc.is_def_eq(&second, &false_));
                assert!(!tc.is_def_eq(&second, &Expr::const_str("Bool.true")));
            }
            println!("FOUNDATION_PROJECTIONS sources=2 checked_roots=12 field_controls=8");
        });
    }
}

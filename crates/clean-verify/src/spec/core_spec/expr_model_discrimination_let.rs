// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Let-constructor discrimination and injectivity lemmas (let promotion, task #28).
//!
//! The genuine `KExpr.let_` constructor is shape-disjoint from every other
//! constructor; the par-reduction inversion towers (par_reduction.rs,
//! par_reduces_c.rs, complete_development.rs) discharge their let_-headed
//! no-confusion arms through the six `X_ne_Y` lemmas below, and recover the
//! three components of a let-vs-let equation through the `let_inj_*` family.
//! Same large-elimination discriminator / Eq.cong projector patterns as
//! expr_model_discrimination{,_pi,_lam_pi}.rs.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Large-elimination discriminator: Let_ -> Empty, every other ctor -> Nat.
const KEXPR_NOT_LET_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

/// Large-elimination discriminator: App -> Empty, every other ctor -> Nat.
const KEXPR_NOT_APP_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

/// Large-elimination discriminator: Lam -> Empty, every other ctor -> Nat.
const KEXPR_NOT_LAM_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

/// Large-elimination discriminator: Pi -> Empty, every other ctor -> Nat.
const KEXPR_NOT_PI_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

/// Large-elimination discriminator: Proj -> Empty, every other ctor -> Nat.
const KEXPR_NOT_PROJ_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) ",
    "(fun (_ : Nat) => Nat))"
);

impl Specification {
    pub(super) fn add_expr_model_let_discrimination(&mut self) -> Result<(), SpecError> {
        self.add_let_discr_ne()?;
        self.add_let_inj_proofs()?;
        Ok(())
    }

    fn add_let_discr_ne(&mut self) -> Result<(), SpecError> {
        // The six no-confusion lemmas. Source args first, target args second,
        // continuation-passing result type R (matching app_ne_lam / pi_ne_lam).
        // Each transports the discriminator's Nat.zero witness along h into
        // Empty and eliminates.
        struct NeCase {
            name: &'static str,
            binders: &'static str,
            lhs: &'static str,
            rhs: &'static str,
            discr: &'static str,
            desc: &'static str,
        }
        let cases = [
            NeCase {
                name: "let_ne_app",
                binders: "(ty : KExpr) (val : KExpr) (body : KExpr) (f : KExpr) (a : KExpr)",
                lhs: "(KExpr.let_ ty val body)",
                rhs: "(KExpr.app f a)",
                discr: KEXPR_NOT_APP_INLINE,
                desc: "Let_ ≠ App discrimination (let promotion, task #28).",
            },
            NeCase {
                name: "let_ne_lam",
                binders: "(ty : KExpr) (val : KExpr) (body : KExpr) (A : KExpr) (b : KExpr)",
                lhs: "(KExpr.let_ ty val body)",
                rhs: "(KExpr.lam A b)",
                discr: KEXPR_NOT_LAM_INLINE,
                desc: "Let_ ≠ Lam discrimination (let promotion, task #28).",
            },
            NeCase {
                name: "let_ne_pi",
                binders: "(ty : KExpr) (val : KExpr) (body : KExpr) (A : KExpr) (B : KExpr)",
                lhs: "(KExpr.let_ ty val body)",
                rhs: "(KExpr.pi A B)",
                discr: KEXPR_NOT_PI_INLINE,
                desc: "Let_ ≠ Pi discrimination (let promotion, task #28).",
            },
            NeCase {
                name: "app_ne_let",
                binders: "(f : KExpr) (a : KExpr) (ty : KExpr) (val : KExpr) (body : KExpr)",
                lhs: "(KExpr.app f a)",
                rhs: "(KExpr.let_ ty val body)",
                discr: KEXPR_NOT_LET_INLINE,
                desc: "App ≠ Let_ discrimination (let promotion, task #28).",
            },
            NeCase {
                name: "lam_ne_let",
                binders: "(A : KExpr) (b : KExpr) (ty : KExpr) (val : KExpr) (body : KExpr)",
                lhs: "(KExpr.lam A b)",
                rhs: "(KExpr.let_ ty val body)",
                discr: KEXPR_NOT_LET_INLINE,
                desc: "Lam ≠ Let_ discrimination (let promotion, task #28).",
            },
            NeCase {
                name: "pi_ne_let",
                binders: "(A : KExpr) (B : KExpr) (ty : KExpr) (val : KExpr) (body : KExpr)",
                lhs: "(KExpr.pi A B)",
                rhs: "(KExpr.let_ ty val body)",
                discr: KEXPR_NOT_LET_INLINE,
                desc: "Pi ≠ Let_ discrimination (let promotion, task #28).",
            },
            NeCase {
                name: "proj_ne_app",
                binders: "(s : Name) (i : Nat) (sub : KExpr) (f : KExpr) (a : KExpr)",
                lhs: "(KExpr.proj s i sub)",
                rhs: "(KExpr.app f a)",
                discr: KEXPR_NOT_APP_INLINE,
                desc: "Proj ≠ App discrimination (proj/lit fragment rung).",
            },
            NeCase {
                name: "proj_ne_lam",
                binders: "(s : Name) (i : Nat) (sub : KExpr) (A : KExpr) (b : KExpr)",
                lhs: "(KExpr.proj s i sub)",
                rhs: "(KExpr.lam A b)",
                discr: KEXPR_NOT_LAM_INLINE,
                desc: "Proj ≠ Lam discrimination (proj/lit fragment rung).",
            },
            NeCase {
                name: "proj_ne_pi",
                binders: "(s : Name) (i : Nat) (sub : KExpr) (A : KExpr) (B : KExpr)",
                lhs: "(KExpr.proj s i sub)",
                rhs: "(KExpr.pi A B)",
                discr: KEXPR_NOT_PI_INLINE,
                desc: "Proj ≠ Pi discrimination (proj/lit fragment rung).",
            },
            NeCase {
                name: "proj_ne_let",
                binders:
                    "(s : Name) (i : Nat) (sub : KExpr) (ty : KExpr) (val : KExpr) (body : KExpr)",
                lhs: "(KExpr.proj s i sub)",
                rhs: "(KExpr.let_ ty val body)",
                discr: KEXPR_NOT_LET_INLINE,
                desc: "Proj ≠ Let_ discrimination (proj/lit fragment rung).",
            },
            NeCase {
                name: "app_ne_proj",
                binders: "(f : KExpr) (a : KExpr) (s : Name) (i : Nat) (sub : KExpr)",
                lhs: "(KExpr.app f a)",
                rhs: "(KExpr.proj s i sub)",
                discr: KEXPR_NOT_PROJ_INLINE,
                desc: "App ≠ Proj discrimination (proj/lit fragment rung).",
            },
            NeCase {
                name: "lam_ne_proj",
                binders: "(A : KExpr) (b : KExpr) (s : Name) (i : Nat) (sub : KExpr)",
                lhs: "(KExpr.lam A b)",
                rhs: "(KExpr.proj s i sub)",
                discr: KEXPR_NOT_PROJ_INLINE,
                desc: "Lam ≠ Proj discrimination (proj/lit fragment rung).",
            },
            NeCase {
                name: "pi_ne_proj",
                binders: "(A : KExpr) (B : KExpr) (s : Name) (i : Nat) (sub : KExpr)",
                lhs: "(KExpr.pi A B)",
                rhs: "(KExpr.proj s i sub)",
                discr: KEXPR_NOT_PROJ_INLINE,
                desc: "Pi ≠ Proj discrimination (proj/lit fragment rung).",
            },
            NeCase {
                name: "let_ne_proj",
                binders:
                    "(ty : KExpr) (val : KExpr) (body : KExpr) (s : Name) (i : Nat) (sub : KExpr)",
                lhs: "(KExpr.let_ ty val body)",
                rhs: "(KExpr.proj s i sub)",
                discr: KEXPR_NOT_PROJ_INLINE,
                desc: "Let_ ≠ Proj discrimination (proj/lit fragment rung).",
            },
        ];
        for c in cases {
            self.add_definition(SpecDefinition {
                name: c.name.to_string(),
                type_src: format!(
                    "forall {binders} (R : Type), Eq KExpr {lhs} {rhs} -> R",
                    binders = c.binders,
                    lhs = c.lhs,
                    rhs = c.rhs,
                ),
                value_src: Some(format!(
                    "fun {binders} (R : Type) (h : Eq KExpr {lhs} {rhs}) => \
                     Empty.rec (fun (_ : Empty) => R) \
                     (Eq.substType KExpr {discr} {lhs} {rhs} h Nat.zero)",
                    binders = c.binders,
                    lhs = c.lhs,
                    rhs = c.rhs,
                    discr = c.discr,
                )),
                is_axiom: false,
                description: c.desc.to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "KExpr.rec".to_string(),
                    "Eq.substType".to_string(),
                    "Empty.rec".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }

    fn add_let_inj_proofs(&mut self) -> Result<(), SpecError> {
        // let_inj_fst / let_inj_snd / let_inj_thd: component recovery from a
        // let-vs-let equation, via Eq.cong with an inline KExpr.rec projector
        // (default = the corresponding lhs component), mirroring lam_inj_fst.
        struct InjCase {
            name: &'static str,
            /// Which projector arm variable to return in the let_ minor.
            proj_var: &'static str,
            /// The default (lhs component) name in the proof term.
            default: &'static str,
            /// Concluded component equation.
            concl: &'static str,
            desc: &'static str,
        }
        let cases = [
            InjCase {
                name: "let_inj_fst",
                proj_var: "(fun (t : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => t)",
                default: "t1",
                concl: "Eq KExpr t1 t2",
                desc: "Let_ injectivity (fst): let_ t1 v1 b1 = let_ t2 v2 b2 -> t1 = t2 (let promotion, task #28).",
            },
            InjCase {
                name: "let_inj_snd",
                proj_var: "(fun (_ : KExpr) (v : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => v)",
                default: "v1",
                concl: "Eq KExpr v1 v2",
                desc: "Let_ injectivity (snd): let_ t1 v1 b1 = let_ t2 v2 b2 -> v1 = v2 (let promotion, task #28).",
            },
            InjCase {
                name: "let_inj_thd",
                proj_var: "(fun (_ : KExpr) (_ : KExpr) (b : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => b)",
                default: "b1",
                concl: "Eq KExpr b1 b2",
                desc: "Let_ injectivity (thd): let_ t1 v1 b1 = let_ t2 v2 b2 -> b1 = b2 (let promotion, task #28).",
            },
        ];
        for c in cases {
            self.add_definition(SpecDefinition {
                name: c.name.to_string(),
                type_src: format!(
                    "forall (t1 : KExpr) (v1 : KExpr) (b1 : KExpr) (t2 : KExpr) (v2 : KExpr) (b2 : KExpr), \
                     Eq KExpr (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2) -> {concl}",
                    concl = c.concl,
                ),
                value_src: Some(format!(
                    "fun (t1 : KExpr) (v1 : KExpr) (b1 : KExpr) (t2 : KExpr) (v2 : KExpr) (b2 : KExpr) \
                     (h : Eq KExpr (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2)) => \
                     Eq.cong KExpr KExpr \
                     (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => KExpr) \
                       (fun (_ : Level) => {default}) \
                       (fun (_ : Nat) => {default}) \
                       (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => {default}) \
                       (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => {default}) \
                       (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => {default}) \
                       (fun (_ : Name) (_ : ListType Level) => {default}) \
                       {proj} \
                       (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : KExpr) => {default}) \
                       (fun (_ : Nat) => {default}) \
                       e) \
                     (KExpr.let_ t1 v1 b1) (KExpr.let_ t2 v2 b2) h",
                    default = c.default,
                    proj = c.proj_var,
                )),
                is_axiom: false,
                description: c.desc.to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "KExpr.rec".to_string(),
                    "Eq.cong".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        self.add_proj_inj_proofs()?;
        Ok(())
    }

    fn add_proj_inj_proofs(&mut self) -> Result<(), SpecError> {
        // proj_inj_name / proj_inj_idx / proj_inj_sub: component recovery from a
        // proj-vs-proj equation, via Eq.cong with an inline KExpr.rec projector
        // landing in Name / Nat / KExpr respectively (proj arm returns the
        // component; every other arm returns a default). Mirrors let_inj_* /
        // kexpr_bvar_inj. Part of the proj/lit fragment rung.
        struct ProjInjCase {
            name: &'static str,
            /// The projector's codomain sort (Name / Nat / KExpr).
            motive_ty: &'static str,
            /// The default value returned by every non-proj arm.
            default: &'static str,
            /// The proj arm (returns the recovered component).
            proj_arm: &'static str,
            /// Concluded component equation.
            concl: &'static str,
            desc: &'static str,
        }
        let cases = [
            ProjInjCase {
                name: "proj_inj_name",
                motive_ty: "Name",
                default: "Name.anonymous",
                proj_arm: "(fun (nm : Name) (_ : Nat) (_ : KExpr) (_ : Name) => nm)",
                concl: "Eq Name s1 s2",
                desc: "Proj injectivity (name): proj s1 i1 sub1 = proj s2 i2 sub2 -> s1 = s2 (proj/lit fragment rung).",
            },
            ProjInjCase {
                name: "proj_inj_idx",
                motive_ty: "Nat",
                default: "Nat.zero",
                proj_arm: "(fun (_ : Name) (idx : Nat) (_ : KExpr) (_ : Nat) => idx)",
                concl: "Eq Nat i1 i2",
                desc: "Proj injectivity (idx): proj s1 i1 sub1 = proj s2 i2 sub2 -> i1 = i2 (proj/lit fragment rung).",
            },
            ProjInjCase {
                name: "proj_inj_sub",
                motive_ty: "KExpr",
                default: "sub1",
                proj_arm: "(fun (_ : Name) (_ : Nat) (sub : KExpr) (_ : KExpr) => sub)",
                concl: "Eq KExpr sub1 sub2",
                desc: "Proj injectivity (sub): proj s1 i1 sub1 = proj s2 i2 sub2 -> sub1 = sub2 (proj/lit fragment rung).",
            },
        ];
        for c in cases {
            self.add_definition(SpecDefinition {
                name: c.name.to_string(),
                type_src: format!(
                    "forall (s1 : Name) (i1 : Nat) (sub1 : KExpr) (s2 : Name) (i2 : Nat) (sub2 : KExpr), \
                     Eq KExpr (KExpr.proj s1 i1 sub1) (KExpr.proj s2 i2 sub2) -> {concl}",
                    concl = c.concl,
                ),
                value_src: Some(format!(
                    "fun (s1 : Name) (i1 : Nat) (sub1 : KExpr) (s2 : Name) (i2 : Nat) (sub2 : KExpr) \
                     (h : Eq KExpr (KExpr.proj s1 i1 sub1) (KExpr.proj s2 i2 sub2)) => \
                     Eq.cong KExpr {mty} \
                     (fun (e : KExpr) => KExpr.rec (fun (_ : KExpr) => {mty}) \
                       (fun (_ : Level) => {default}) \
                       (fun (_ : Nat) => {default}) \
                       (fun (_ : KExpr) (_ : KExpr) (_ : {mty}) (_ : {mty}) => {default}) \
                       (fun (_ : KExpr) (_ : KExpr) (_ : {mty}) (_ : {mty}) => {default}) \
                       (fun (_ : KExpr) (_ : KExpr) (_ : {mty}) (_ : {mty}) => {default}) \
                       (fun (_ : Name) (_ : ListType Level) => {default}) \
                       (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : {mty}) (_ : {mty}) (_ : {mty}) => {default}) \
                       {proj_arm} \
                       (fun (_ : Nat) => {default}) \
                       e) \
                     (KExpr.proj s1 i1 sub1) (KExpr.proj s2 i2 sub2) h",
                    mty = c.motive_ty,
                    default = c.default,
                    proj_arm = c.proj_arm,
                )),
                is_axiom: false,
                description: c.desc.to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "KExpr.rec".to_string(),
                    "Eq.cong".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }
}

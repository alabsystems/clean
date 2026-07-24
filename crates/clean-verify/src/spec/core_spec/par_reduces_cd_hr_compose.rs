// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H++ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 4,
//! the HINDLEY-ROSEN assembly): the closure-coincidence SANDWICH that bridges the
//! abstract macro confluence `mstar_confluent_of` to the named 3-way target
//! `par_reduces_cd_star_diamond` (modulo the β+ι/δ commutation).
//!
//! ## The sandwich (blueprint §(b), the `MStar` ↔ `StepStar` inter-derivability)
//!
//! The blueprint transports an arbitrary pair of union reductions into `MStar`,
//! applies `MStar_confluent`, and transports back, because `MStar` (= the closure
//! of `ParStar ∪ DeltaStar`) and the union closure `StepStar` are inter-derivable.
//! In the in-tree encoding the union closure is `par_reduces_cd_star` (the RT-closure
//! of the atomic 3-way `par_reduces_cd`), and `m_star` is the closure of the macro
//! step. The two coincide:
//!   - `m_star ⊆ par_reduces_cd_star` (`m_star_to_cd_star`): each macro step is a
//!     `par_reduces_c_star` block (⊆ `par_reduces_cd_star`, via the lifted
//!     `par_reduces_c_subsumes_cd`) or a `delta_cong_star` block (⊆ via the landed
//!     `delta_cong_star_subsumes_cd_star`);
//!   - `par_reduces_cd_star ⊆ m_star` (`par_reduces_cd_star_subsumes_m_star`): each
//!     atomic 3-way step decomposes into a finite macro reduction — the congruence
//!     cases via the macro congruences `m_star_{app,lam,pi,let}`, the β contraction
//!     via one `par_reduces_c.beta` fire and the ζ contraction via one
//!     `par_reduces_c.let_` fire (one macro step each, at the GENUINE `KExpr.let_`
//!     node), iota/delta via a single `par_reduces_c.iota` / `delta_cong.here`
//!     embed. (`forall_` still goes through the `pi` reducible alias; `let_` is a
//!     genuine 7th ctor since the let promotion, task #28.)
//!
//! With the sandwich, `par_reduces_cd_star_diamond_of_commute` discharges the two
//! landed corners (β+ι CR `par_reduces_c_star_diamond` carrying its four faithful
//! `RecEnv` interfaces, δ CR `delta_cong_star_diamond`) and carries the β+ι/δ
//! commutation `COMM` as the SOLE remaining bound hypothesis — the Hindley-Rosen
//! 3-way Church-Rosser ISOLATED to exactly the commutation. The genuine named
//! `par_reduces_cd_star_diamond` lands once `COMM` is discharged by a proven
//! commutation (the remaining obligation).
//!
//! Runs AFTER `add_par_reduces_cd_hr` (the abstract combinators) and reuses the
//! `par_reduces_cd_star` substrate from `add_par_reduces_pd`, the embeddings from
//! `add_par_reduces_d` / `add_par_reduces_cd`, and the landed CRs. Part of #2859
//! (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// One macro congruence: `(name, head, par_cong, delta_cong, vary_first, fixed)`.
/// `vary_first` = whether the reduced subterm is the FIRST ctor slot; `fixed` =
/// the binder name of the untouched slot.
const MACRO_CONG_ARMS: [(&str, &str, &str, &str, &str, bool, &str); 6] = [
    (
        "appL",
        "KExpr.app",
        "par_reduces_c_star_app",
        "delta_cong_star_app",
        "app",
        true,
        "a",
    ),
    (
        "appR",
        "KExpr.app",
        "par_reduces_c_star_app",
        "delta_cong_star_app",
        "app",
        false,
        "f",
    ),
    (
        "lamL",
        "KExpr.lam",
        "par_reduces_c_star_lam",
        "delta_cong_star_lam",
        "lam",
        true,
        "body",
    ),
    (
        "lamR",
        "KExpr.lam",
        "par_reduces_c_star_lam",
        "delta_cong_star_lam",
        "lam",
        false,
        "ty",
    ),
    (
        "piL",
        "KExpr.pi",
        "par_reduces_c_star_pi",
        "delta_cong_star_pi",
        "pi",
        true,
        "body",
    ),
    (
        "piR",
        "KExpr.pi",
        "par_reduces_c_star_pi",
        "delta_cong_star_pi",
        "pi",
        false,
        "dom",
    ),
];

impl Specification {
    pub(super) fn add_par_reduces_cd_hr_compose(&mut self) -> Result<(), SpecError> {
        self.add_m_step_congruences()?;
        self.add_m_star_congruences()?;
        self.add_m_star_compound_congruences()?;
        self.add_let_macro_congruences()?;
        self.add_hr_cd_star_embeddings()?;
        self.add_par_reduces_cd_subsumes_m_star()?;
        self.add_par_strips_witness_cd_star()?;
        self.add_par_reduces_cd_star_diamond_of_commute()?;
        self.add_par_reduces_cd_star_diamond_of_sc()?;
        Ok(())
    }

    /// Brick D8: `par_reduces_cd_star_diamond_of_sc` — the 3-way (β+ι+δ) Church-Rosser
    /// of `par_reduces_cd_star`, ISOLATED to the single-step strong commutation `SC`.
    /// Discharges the commutation hypothesis `COMM` of
    /// `par_reduces_cd_star_diamond_of_commute` with the star-tiled
    /// `par_delta_commute_of_sc env SC`, leaving the four faithful `RecEnv` interfaces
    /// and `SC` (the single-step β+ι/δ strong commutation) as the only bound
    /// hypotheses — directly mirroring how δ Church-Rosser was isolated to its
    /// single-step diamond (`delta_cong_star_diamond_of_strong`'s `SC`). The genuine
    /// unconditional named `par_reduces_cd_star_diamond` lands once `SC` is discharged
    /// by a proof of the single-step β+ι/δ strong commutation (the sole remaining
    /// obligation).
    fn add_par_reduces_cd_star_diamond_of_sc(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_diamond_of_sc".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) ",
                "(i1 : RecEnvReductNotRedex (red_rec env)) (i2 : RecEnvCtorNoRecMeta (red_rec env)) ",
                "(i3 : RecEnvClosed (red_rec env)) (i4 : RecEnvLiftClosed (red_rec env)) ",
                "(SC : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
                "par_reduces_c (red_rec env) s u -> delta_cong env s v -> par_delta_sc_witness env u v) ",
                "(e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_cd_star env e e1 -> par_reduces_cd_star env e e2 -> ",
                "par_strips_witness_cd_star env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) ",
                    "(i1 : RecEnvReductNotRedex (red_rec env)) (i2 : RecEnvCtorNoRecMeta (red_rec env)) ",
                    "(i3 : RecEnvClosed (red_rec env)) (i4 : RecEnvLiftClosed (red_rec env)) ",
                    "(SC : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
                    "par_reduces_c (red_rec env) s u -> delta_cong env s v -> par_delta_sc_witness env u v) ",
                    "(e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : par_reduces_cd_star env e e1) (h2 : par_reduces_cd_star env e e2) => ",
                    "par_reduces_cd_star_diamond_of_commute env i1 i2 i3 i4 ",
                    "(par_delta_commute_of_sc env SC) e e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "par_reduces_cd_star_diamond_of_sc — the 3-way (β+ι+δ) Church-Rosser of par_reduces_cd_star, ",
                "ISOLATED to the single-step strong commutation SC. Discharges the COMM hypothesis of ",
                "par_reduces_cd_star_diamond_of_commute with the star-tiled par_delta_commute_of_sc env SC, ",
                "leaving the four faithful RecEnv interfaces and SC (the single-step β+ι/δ strong commutation) as ",
                "the ONLY bound hypotheses — mirroring how δ CR was isolated to its single-step diamond. The ",
                "genuine unconditional par_reduces_cd_star_diamond lands once SC is discharged. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_diamond_of_commute".to_string(),
                "par_delta_commute_of_sc".to_string(),
                "par_delta_sc_witness".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "par_reduces_c".to_string(),
                "delta_cong".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick D1: the six single-macro-step congruences `m_step_{appL,appR,lamL,lamR,
    /// piL,piR}`. A macro step on a subterm lifts to a macro step on the compound
    /// term (other slot fixed): `@m_step.rec` dispatches the `par` leg through the
    /// matching `par_reduces_c_star_<head>` (refl on the fixed slot) and the `delta`
    /// leg through `delta_cong_star_<head>`.
    fn add_m_step_congruences(&mut self) -> Result<(), SpecError> {
        for (suffix, head, par_cong, delta_cong, _label, vary_first, fixed) in MACRO_CONG_ARMS {
            let name = format!("m_step_{suffix}");
            let wrap = |x: &str| {
                if vary_first {
                    format!("({head} {x} {fixed})")
                } else {
                    format!("({head} {fixed} {x})")
                }
            };
            let par_leg = if vary_first {
                format!(
                    "({par_cong} (red_rec env) u0 u1 {fixed} {fixed} hp (par_reduces_c_star.refl (red_rec env) {fixed}))"
                )
            } else {
                format!(
                    "({par_cong} (red_rec env) {fixed} {fixed} u0 u1 (par_reduces_c_star.refl (red_rec env) {fixed}) hp)"
                )
            };
            let delta_leg = if vary_first {
                format!(
                    "({delta_cong} env u0 u1 {fixed} {fixed} hd (delta_cong_star.refl env {fixed}))"
                )
            } else {
                format!(
                    "({delta_cong} env {fixed} {fixed} u0 u1 (delta_cong_star.refl env {fixed}) hd)"
                )
            };
            let type_src = format!(
                "forall (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({fixed} : KExpr), \
                 m_step env u0 u1 -> m_step env {w0} {w1}",
                w0 = wrap("u0"),
                w1 = wrap("u1"),
            );
            let value_src = format!(
                "fun (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({fixed} : KExpr) (h : m_step env u0 u1) => \
                 @m_step.rec env u0 u1 (fun (_ : m_step env u0 u1) => m_step env {w0} {w1}) \
                 (fun (hp : par_reduces_c_star (red_rec env) u0 u1) => m_step.par env {w0} {w1} {par_leg}) \
                 (fun (hd : delta_cong_star env u0 u1) => m_step.delta env {w0} {w1} {delta_leg}) \
                 h",
                w0 = wrap("u0"),
                w1 = wrap("u1"),
                par_leg = par_leg,
                delta_leg = delta_leg,
            );
            self.add_definition(SpecDefinition {
                name: name.clone(),
                type_src,
                value_src: Some(value_src),
                is_axiom: false,
                description: format!(
                    "Single-macro-step congruence {name}: a macro step on a subterm lifts to a macro step on \
                     the compound {head} (other slot fixed). @m_step.rec dispatches the par leg through \
                     {par_cong} (refl on the fixed slot) and the delta leg through {delta_cong}. DerivedProved, \
                     zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "m_step".to_string(),
                    "m_step.rec".to_string(),
                    "m_step.par".to_string(),
                    "m_step.delta".to_string(),
                    "par_reduces_c_star".to_string(),
                    "par_reduces_c_star.refl".to_string(),
                    "delta_cong_star".to_string(),
                    "delta_cong_star.refl".to_string(),
                    par_cong.to_string(),
                    delta_cong.to_string(),
                    "red_rec".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }

    /// Brick D2: the six macro-star congruences `m_star_{appL,appR,lamL,lamR,piL,piR}`
    /// — lift each `m_step_<X>` over the macro closure `m_star` (induction on the
    /// closure, prefixing each lifted head step). Mirror of `delta_cong_star_app`'s
    /// one-sided shape.
    fn add_m_star_congruences(&mut self) -> Result<(), SpecError> {
        for (suffix, head, _par_cong, _delta_cong, _label, vary_first, fixed) in MACRO_CONG_ARMS {
            let name = format!("m_star_{suffix}");
            let step_name = format!("m_step_{suffix}");
            let wrap = |x: &str| {
                if vary_first {
                    format!("({head} {x} {fixed})")
                } else {
                    format!("({head} {fixed} {x})")
                }
            };
            let type_src = format!(
                "forall (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({fixed} : KExpr), \
                 m_star env u0 u1 -> m_star env {w0} {w1}",
                w0 = wrap("u0"),
                w1 = wrap("u1"),
            );
            let value_src = format!(
                "fun (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({fixed} : KExpr) (h : m_star env u0 u1) => \
                 m_star.rec env \
                 (fun (x : KExpr) (y : KExpr) (_ : m_star env x y) => m_star env {wx} {wy}) \
                 (fun (e : KExpr) => m_star.refl env {we}) \
                 (fun (x : KExpr) (x1 : KExpr) (x2 : KExpr) \
                 (hstep : m_step env x x1) (_htail : m_star env x1 x2) (ih : m_star env {wx1} {wx2}) => \
                 m_star.step env {wx} {wx1} {wx2} ({step_name} env x x1 {fixed} hstep) ih) \
                 u0 u1 h",
                wx = wrap("x"),
                wy = wrap("y"),
                we = wrap("e"),
                wx1 = wrap("x1"),
                wx2 = wrap("x2"),
                step_name = step_name,
            );
            self.add_definition(SpecDefinition {
                name: name.clone(),
                type_src,
                value_src: Some(value_src),
                is_axiom: false,
                description: format!(
                    "Macro-star congruence {name}: lift {step_name} over the macro closure m_star (m_star.rec \
                     induction, prefixing each lifted head step). DerivedProved, zero axiom_deps. Part of #2859 \
                     (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "m_step".to_string(),
                    "m_star".to_string(),
                    "m_star.rec".to_string(),
                    "m_star.refl".to_string(),
                    "m_star.step".to_string(),
                    step_name,
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }

    /// Brick D3: the compound macro congruences `m_star_{app,lam,pi}` — both slots
    /// reduce, composed by `m_star_trans` through the intermediate (first slot done,
    /// second pending). Mirror of `par_reduces_cd_star_app`.
    fn add_m_star_compound_congruences(&mut self) -> Result<(), SpecError> {
        // (name, head, L-lift, R-lift, first-binders, second-binders)
        for (name, head, lift_l, lift_r, s0, s0p, s1, s1p) in [
            (
                "m_star_app",
                "KExpr.app",
                "m_star_appL",
                "m_star_appR",
                "f",
                "f'",
                "a",
                "a'",
            ),
            (
                "m_star_lam",
                "KExpr.lam",
                "m_star_lamL",
                "m_star_lamR",
                "ty",
                "ty'",
                "body",
                "body'",
            ),
            (
                "m_star_pi",
                "KExpr.pi",
                "m_star_piL",
                "m_star_piR",
                "dom",
                "dom'",
                "body",
                "body'",
            ),
        ] {
            let type_src = format!(
                "forall (env : RedEnv) ({s0} : KExpr) ({s0p} : KExpr) ({s1} : KExpr) ({s1p} : KExpr), \
                 m_star env {s0} {s0p} -> m_star env {s1} {s1p} -> \
                 m_star env ({head} {s0} {s1}) ({head} {s0p} {s1p})"
            );
            // L-lift varies the first slot (fixed = the second, here s1); R-lift varies
            // the second slot (fixed = the first, here s0p after the first leg).
            let value_src = format!(
                "fun (env : RedEnv) ({s0} : KExpr) ({s0p} : KExpr) ({s1} : KExpr) ({s1p} : KExpr) \
                 (h0 : m_star env {s0} {s0p}) (h1 : m_star env {s1} {s1p}) => \
                 m_star_trans env ({head} {s0} {s1}) ({head} {s0p} {s1}) ({head} {s0p} {s1p}) \
                 ({lift_l} env {s0} {s0p} {s1} h0) \
                 ({lift_r} env {s1} {s1p} {s0p} h1)"
            );
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src,
                value_src: Some(value_src),
                is_axiom: false,
                description: format!(
                    "Compound macro congruence {name}: both slots reduce, composed by m_star_trans through the \
                     first-slot-done intermediate ({lift_l} then {lift_r}). Mirror of par_reduces_cd_star_app. \
                     DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — \
                     Hindley-Rosen assembly)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "m_star".to_string(),
                    "m_star_trans".to_string(),
                    lift_l.to_string(),
                    lift_r.to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }
        Ok(())
    }

    /// Brick D3L (let promotion, task #28): the LET macro congruence tower over the
    /// genuine 3-slot `KExpr.let_` node —
    ///   - `m_step_{letL,letV,letB}` — one-slot single-macro-step congruences (the
    ///     let analogue of Brick D1), dispatching the par leg through the landed
    ///     `par_reduces_c_star_let_cong` and the delta leg through the landed
    ///     `delta_cong_star_let` (`par_reduces_d.rs`), refl on the fixed slots;
    ///   - `m_star_{letL,letV,letB}` — their closure lifts (Brick D2 analogue);
    ///   - `m_star_let` — the compound 3-slot macro congruence (Brick D3 analogue),
    ///     two `m_star_trans` through the waypoints.
    /// Feeds the `let_`/`let_cong` arms of `par_reduces_cd_subsumes_m_star`.
    fn add_let_macro_congruences(&mut self) -> Result<(), SpecError> {
        // m_step_letL / m_step_letV / m_step_letB: one-slot single-macro-step let
        // congruences. (varying slot u0 -> u1; fixed slots f0/f1 in ctor-position
        // order; wrap places the varying slot at its position.)
        struct LetSlot {
            suffix: &'static str,
            /// wrap("x") = the let_ node with the varying slot at `x`.
            wrap: fn(&str) -> String,
            /// The two fixed binder names, in binder order.
            f0: &'static str,
            f1: &'static str,
            /// compound-congruence argument order for (u0 -> u1) with refls on fixed:
            /// (ty ty' val val' body body') as strings over u0/u1/f0/f1.
            par_leg: fn() -> String,
            delta_leg: fn() -> String,
        }
        let slots = [
            LetSlot {
                suffix: "letL",
                wrap: |x| format!("(KExpr.let_ {x} v b)"),
                f0: "v",
                f1: "b",
                par_leg: || {
                    concat!(
                        "(par_reduces_c_star_let_cong (red_rec env) u0 u1 v v b b hp ",
                        "(par_reduces_c_star.refl (red_rec env) v) (par_reduces_c_star.refl (red_rec env) b))"
                    )
                    .to_string()
                },
                delta_leg: || {
                    concat!(
                        "(delta_cong_star_let env u0 u1 v v b b hd ",
                        "(delta_cong_star.refl env v) (delta_cong_star.refl env b))"
                    )
                    .to_string()
                },
            },
            LetSlot {
                suffix: "letV",
                wrap: |x| format!("(KExpr.let_ t {x} b)"),
                f0: "t",
                f1: "b",
                par_leg: || {
                    concat!(
                        "(par_reduces_c_star_let_cong (red_rec env) t t u0 u1 b b ",
                        "(par_reduces_c_star.refl (red_rec env) t) hp (par_reduces_c_star.refl (red_rec env) b))"
                    )
                    .to_string()
                },
                delta_leg: || {
                    concat!(
                        "(delta_cong_star_let env t t u0 u1 b b ",
                        "(delta_cong_star.refl env t) hd (delta_cong_star.refl env b))"
                    )
                    .to_string()
                },
            },
            LetSlot {
                suffix: "letB",
                wrap: |x| format!("(KExpr.let_ t v {x})"),
                f0: "t",
                f1: "v",
                par_leg: || {
                    concat!(
                        "(par_reduces_c_star_let_cong (red_rec env) t t v v u0 u1 ",
                        "(par_reduces_c_star.refl (red_rec env) t) (par_reduces_c_star.refl (red_rec env) v) hp)"
                    )
                    .to_string()
                },
                delta_leg: || {
                    concat!(
                        "(delta_cong_star_let env t t v v u0 u1 ",
                        "(delta_cong_star.refl env t) (delta_cong_star.refl env v) hd)"
                    )
                    .to_string()
                },
            },
        ];
        for s in &slots {
            let name = format!("m_step_{}", s.suffix);
            let w0 = (s.wrap)("u0");
            let w1 = (s.wrap)("u1");
            let type_src = format!(
                "forall (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({f0} : KExpr) ({f1} : KExpr), \
                 m_step env u0 u1 -> m_step env {w0} {w1}",
                f0 = s.f0,
                f1 = s.f1,
            );
            let value_src = format!(
                "fun (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({f0} : KExpr) ({f1} : KExpr) (h : m_step env u0 u1) => \
                 @m_step.rec env u0 u1 (fun (_ : m_step env u0 u1) => m_step env {w0} {w1}) \
                 (fun (hp : par_reduces_c_star (red_rec env) u0 u1) => m_step.par env {w0} {w1} {par_leg}) \
                 (fun (hd : delta_cong_star env u0 u1) => m_step.delta env {w0} {w1} {delta_leg}) \
                 h",
                f0 = s.f0,
                f1 = s.f1,
                par_leg = (s.par_leg)(),
                delta_leg = (s.delta_leg)(),
            );
            self.add_definition(SpecDefinition {
                name: name.clone(),
                type_src,
                value_src: Some(value_src),
                is_axiom: false,
                description: format!(
                    "Single-macro-step let congruence {name}: a macro step on one slot of the genuine let_ node \
                     lifts to a macro step on the compound (other slots fixed). @m_step.rec dispatches the par leg \
                     through par_reduces_c_star_let_cong and the delta leg through delta_cong_star_let, refls \
                     on the fixed slots. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta \
                     increment Stage 4 — let promotion, task #28)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "m_step".to_string(),
                    "m_step.rec".to_string(),
                    "m_step.par".to_string(),
                    "m_step.delta".to_string(),
                    "par_reduces_c_star".to_string(),
                    "par_reduces_c_star.refl".to_string(),
                    "par_reduces_c_star_let_cong".to_string(),
                    "delta_cong_star".to_string(),
                    "delta_cong_star.refl".to_string(),
                    "delta_cong_star_let".to_string(),
                    "red_rec".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // m_star_letL / m_star_letV / m_star_letB: lift each m_step_letX over m_star.
        for s in &slots {
            let name = format!("m_star_{}", s.suffix);
            let step_name = format!("m_step_{}", s.suffix);
            let w0 = (s.wrap)("u0");
            let w1 = (s.wrap)("u1");
            let type_src = format!(
                "forall (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({f0} : KExpr) ({f1} : KExpr), \
                 m_star env u0 u1 -> m_star env {w0} {w1}",
                f0 = s.f0,
                f1 = s.f1,
            );
            let value_src = format!(
                "fun (env : RedEnv) (u0 : KExpr) (u1 : KExpr) ({f0} : KExpr) ({f1} : KExpr) (h : m_star env u0 u1) => \
                 m_star.rec env \
                 (fun (x : KExpr) (y : KExpr) (_ : m_star env x y) => m_star env {wx} {wy}) \
                 (fun (e : KExpr) => m_star.refl env {we}) \
                 (fun (x : KExpr) (x1 : KExpr) (x2 : KExpr) \
                 (hstep : m_step env x x1) (_htail : m_star env x1 x2) (ih : m_star env {wx1} {wx2}) => \
                 m_star.step env {wx} {wx1} {wx2} ({step_name} env x x1 {f0} {f1} hstep) ih) \
                 u0 u1 h",
                f0 = s.f0,
                f1 = s.f1,
                wx = (s.wrap)("x"),
                wy = (s.wrap)("y"),
                we = (s.wrap)("e"),
                wx1 = (s.wrap)("x1"),
                wx2 = (s.wrap)("x2"),
                step_name = step_name,
            );
            self.add_definition(SpecDefinition {
                name: name.clone(),
                type_src,
                value_src: Some(value_src),
                is_axiom: false,
                description: format!(
                    "Macro-star let congruence {name}: lift {step_name} over the macro closure m_star (m_star.rec \
                     induction, prefixing each lifted head step). DerivedProved, zero axiom_deps. Part of #2859 \
                     (Increment H++, delta increment Stage 4 — let promotion, task #28)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "m_step".to_string(),
                    "m_star".to_string(),
                    "m_star.rec".to_string(),
                    "m_star.refl".to_string(),
                    "m_star.step".to_string(),
                    step_name,
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // m_star_let: the compound 3-slot macro congruence — all three slots reduce,
        // composed by two m_star_trans through the ty-done and ty+val-done waypoints.
        self.add_definition(SpecDefinition {
            name: "m_star_let".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), ",
                "m_star env ty ty' -> m_star env val val' -> m_star env body body' -> ",
                "m_star env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body')"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
                    "(h0 : m_star env ty ty') (h1 : m_star env val val') (h2 : m_star env body body') => ",
                    "m_star_trans env (KExpr.let_ ty val body) (KExpr.let_ ty' val body) (KExpr.let_ ty' val' body') ",
                    "(m_star_letL env ty ty' val body h0) ",
                    "(m_star_trans env (KExpr.let_ ty' val body) (KExpr.let_ ty' val' body) (KExpr.let_ ty' val' body') ",
                    "(m_star_letV env val val' ty' body h1) ",
                    "(m_star_letB env body body' ty' val' h2))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Compound macro let congruence m_star_let: all three slots of the genuine let_ node reduce, ",
                "composed by two m_star_trans through the ty-done (let_ ty' val body) and ty+val-done ",
                "(let_ ty' val' body) waypoints (m_star_letL then m_star_letV then m_star_letB). The let analogue ",
                "of m_star_{app,lam,pi}. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta ",
                "increment Stage 4 — let promotion, task #28)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_star".to_string(),
                "m_star_trans".to_string(),
                "m_star_letL".to_string(),
                "m_star_letV".to_string(),
                "m_star_letB".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // m_step_proj: single-macro-step proj congruence over the genuine 1-slot
        // proj node (Name/Nat carried through, scrutinee reduces). @m_step.rec
        // dispatches the par leg through par_reduces_c_star_proj and the delta leg
        // through delta_cong_star_proj. Part of the proj/lit fragment rung.
        self.add_definition(SpecDefinition {
            name: "m_step_proj".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (s : Name) (i : Nat) (u0 : KExpr) (u1 : KExpr), ",
                "m_step env u0 u1 -> m_step env (KExpr.proj s i u0) (KExpr.proj s i u1)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (s : Name) (i : Nat) (u0 : KExpr) (u1 : KExpr) ",
                    "(h : m_step env u0 u1) => ",
                    "@m_step.rec env u0 u1 ",
                    "(fun (_ : m_step env u0 u1) => m_step env (KExpr.proj s i u0) (KExpr.proj s i u1)) ",
                    "(fun (hp : par_reduces_c_star (red_rec env) u0 u1) => ",
                    "m_step.par env (KExpr.proj s i u0) (KExpr.proj s i u1) ",
                    "(par_reduces_c_star_proj (red_rec env) s i u0 u1 hp)) ",
                    "(fun (hd : delta_cong_star env u0 u1) => ",
                    "m_step.delta env (KExpr.proj s i u0) (KExpr.proj s i u1) ",
                    "(delta_cong_star_proj env s i u0 u1 hd)) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Single-macro-step proj congruence m_step_proj: a macro step on the scrutinee of the genuine ",
                "1-slot proj node lifts to a macro step on the projection. @m_step.rec dispatches the par leg ",
                "through par_reduces_c_star_proj and the delta leg through delta_cong_star_proj. DerivedProved, ",
                "zero axiom_deps. Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_step".to_string(),
                "m_step.rec".to_string(),
                "m_step.par".to_string(),
                "m_step.delta".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_proj".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star_proj".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // m_star_proj: lift m_step_proj over the macro closure m_star.
        self.add_definition(SpecDefinition {
            name: "m_star_proj".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (s : Name) (i : Nat) (u0 : KExpr) (u1 : KExpr), ",
                "m_star env u0 u1 -> m_star env (KExpr.proj s i u0) (KExpr.proj s i u1)"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (s : Name) (i : Nat) (u0 : KExpr) (u1 : KExpr) ",
                    "(h : m_star env u0 u1) => ",
                    "m_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : m_star env x y) => ",
                    "m_star env (KExpr.proj s i x) (KExpr.proj s i y)) ",
                    "(fun (e : KExpr) => m_star.refl env (KExpr.proj s i e)) ",
                    "(fun (x : KExpr) (x1 : KExpr) (x2 : KExpr) ",
                    "(hstep : m_step env x x1) (_htail : m_star env x1 x2) ",
                    "(ih : m_star env (KExpr.proj s i x1) (KExpr.proj s i x2)) => ",
                    "m_star.step env (KExpr.proj s i x) (KExpr.proj s i x1) (KExpr.proj s i x2) ",
                    "(m_step_proj env s i x x1 hstep) ih) ",
                    "u0 u1 h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Macro-star proj congruence m_star_proj: lift m_step_proj over the macro closure m_star ",
                "(m_star.rec induction, prefixing each lifted head step). The proj analogue of m_star_{app,lam,pi}. ",
                "DerivedProved, zero axiom_deps. Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_step".to_string(),
                "m_star".to_string(),
                "m_star.rec".to_string(),
                "m_star.refl".to_string(),
                "m_star.step".to_string(),
                "m_step_proj".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick D4: the `m_star ↔ par_reduces_cd_star` half of the sandwich —
    /// `par_reduces_c_star_subsumes_cd_star` (lift `par_reduces_c_subsumes_cd` over
    /// the β+ι closure), `m_step_to_cd_star` (a macro step embeds, par via the
    /// previous, delta via the landed `delta_cong_star_subsumes_cd_star`) and
    /// `m_star_to_cd_star` (lift over the macro closure). This is the EASY direction
    /// `m_star ⊆ par_reduces_cd_star`.
    fn add_hr_cd_star_embeddings(&mut self) -> Result<(), SpecError> {
        // par_reduces_c_star_subsumes_cd_star: lift par_reduces_c_subsumes_cd over the
        // β+ι RT-closure.
        self.add_definition(SpecDefinition {
            name: "par_reduces_c_star_subsumes_cd_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_c_star (red_rec env) e e' -> par_reduces_cd_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) ",
                    "(h : par_reduces_c_star (red_rec env) e e') => ",
                    "par_reduces_c_star.rec (red_rec env) ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_c_star (red_rec env) a b) => ",
                    "par_reduces_cd_star env a b) ",
                    "(fun (s : KExpr) => par_reduces_cd_star.refl env s) ",
                    "(fun (s : KExpr) (s' : KExpr) (s'' : KExpr) ",
                    "(hstep : par_reduces_c (red_rec env) s s') (_htail : par_reduces_c_star (red_rec env) s' s'') ",
                    "(ih : par_reduces_cd_star env s' s'') => ",
                    "par_reduces_cd_star.step env s s' s'' ",
                    "(par_reduces_c_subsumes_cd env s s' hstep) ih) ",
                    "e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Star-level embedding par_reduces_c_star (red_rec env) ⊆ par_reduces_cd_star env: lift ",
                "par_reduces_c_subsumes_cd over the β+ι RT-closure (par_reduces_c_star.rec, refl to ",
                "par_reduces_cd_star.refl, step prefixing the embedded single step). DerivedProved, zero ",
                "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star.step".to_string(),
                "par_reduces_c_subsumes_cd".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // m_step_to_cd_star: a macro step embeds into par_reduces_cd_star.
        self.add_definition(SpecDefinition {
            name: "m_step_to_cd_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (a : KExpr) (b : KExpr), ",
                "m_step env a b -> par_reduces_cd_star env a b"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (a : KExpr) (b : KExpr) (h : m_step env a b) => ",
                    "@m_step.rec env a b ",
                    "(fun (_ : m_step env a b) => par_reduces_cd_star env a b) ",
                    "(fun (hp : par_reduces_c_star (red_rec env) a b) => ",
                    "par_reduces_c_star_subsumes_cd_star env a b hp) ",
                    "(fun (hd : delta_cong_star env a b) => ",
                    "delta_cong_star_subsumes_cd_star env a b hd) ",
                    "h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "A macro step embeds into par_reduces_cd_star: @m_step.rec — par via ",
                "par_reduces_c_star_subsumes_cd_star, delta via the landed delta_cong_star_subsumes_cd_star. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — ",
                "Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_step".to_string(),
                "m_step.rec".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_c_star_subsumes_cd_star".to_string(),
                "delta_cong_star_subsumes_cd_star".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // m_star_to_cd_star: lift m_step_to_cd_star over the macro closure.
        self.add_definition(SpecDefinition {
            name: "m_star_to_cd_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (a : KExpr) (b : KExpr), ",
                "m_star env a b -> par_reduces_cd_star env a b"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (a : KExpr) (b : KExpr) (h : m_star env a b) => ",
                    "m_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_ : m_star env x y) => par_reduces_cd_star env x y) ",
                    "(fun (e : KExpr) => par_reduces_cd_star.refl env e) ",
                    "(fun (x : KExpr) (x1 : KExpr) (x2 : KExpr) ",
                    "(hstep : m_step env x x1) (_htail : m_star env x1 x2) ",
                    "(ih : par_reduces_cd_star env x1 x2) => ",
                    "par_reduces_cd_star_trans env x x1 x2 (m_step_to_cd_star env x x1 hstep) ih) ",
                    "a b h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "m_star ⊆ par_reduces_cd_star: lift m_step_to_cd_star over the macro closure (m_star.rec, refl ",
                "to par_reduces_cd_star.refl, step composing the embedded macro step via par_reduces_cd_star_trans). ",
                "The EASY half of the closure-coincidence sandwich. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_step".to_string(),
                "m_star".to_string(),
                "m_star.rec".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.refl".to_string(),
                "par_reduces_cd_star_trans".to_string(),
                "m_step_to_cd_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick D5: the HARD half of the sandwich `par_reduces_cd_star ⊆ m_star`.
    /// `par_reduces_cd_subsumes_m_star` decomposes a single atomic 3-way step into a
    /// finite macro reduction (par_reduces_cd.rec, 10 arms: refl is m_star.refl; the
    /// congruence arms app/lam/pi via m_star_{app,lam,pi}; forall_ via m_star_pi
    /// (the pi reducible alias); beta reduces the subterms via m_star_{app,lam} then
    /// fires one par_reduces_c.beta; let_ (ZETA, at the genuine 7th KExpr ctor)
    /// reduces the three slots via m_star_let then fires one par_reduces_c.let_;
    /// let_cong (the trailing congruence ctor) is m_star_let on the IHs;
    /// iota/delta are a single par_reduces_c.iota / delta_cong.here embed).
    /// `par_reduces_cd_star_subsumes_m_star` lifts it over the closure.
    fn add_par_reduces_cd_subsumes_m_star(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_subsumes_m_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_cd env e e' -> m_star env e e'"
            )
            .to_string(),
            value_src: Some(par_reduces_cd_subsumes_m_star_proof()),
            is_axiom: false,
            description: concat!(
                "par_reduces_cd ⊆ m_star: a single atomic 3-way step decomposes into a finite macro reduction. ",
                "par_reduces_cd.rec — refl is m_star.refl; app/lam/pi via the compound macro congruences ",
                "m_star_{app,lam,pi}; forall_ via m_star_pi (the pi reducible alias unfolds by defeq); beta ",
                "reduces the subterms (m_star_app of m_star_lam) then fires one par_reduces_c.beta as one macro ",
                "step; let_ (ZETA, at the genuine 7th KExpr ctor) reduces the three slots via m_star_let then ",
                "fires one par_reduces_c.let_ as one macro step; the trailing let_cong congruence arm is ",
                "m_star_let on the IHs; iota/delta are a single par_reduces_c.iota / delta_cong.here embed. The ",
                "HARD half of the closure-coincidence sandwich. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd.rec".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_c.beta".to_string(),
                "par_reduces_c.let_".to_string(),
                "par_reduces_c.iota".to_string(),
                "par_reduces_c.refl".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "delta_cong".to_string(),
                "delta_cong.here".to_string(),
                "delta_cong_subsumes_star".to_string(),
                "m_step".to_string(),
                "m_step.par".to_string(),
                "m_step.delta".to_string(),
                "m_star".to_string(),
                "m_star.refl".to_string(),
                "m_step_to_mstar".to_string(),
                "m_star_trans".to_string(),
                "m_star_app".to_string(),
                "m_star_lam".to_string(),
                "m_star_pi".to_string(),
                "m_star_let".to_string(),
                "m_star_proj".to_string(),
                "red_rec".to_string(),
                "red_def".to_string(),
                "instantiate".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_cd_star_subsumes_m_star: lift over the closure.
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_subsumes_m_star".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e' : KExpr), ",
                "par_reduces_cd_star env e e' -> m_star env e e'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e' : KExpr) ",
                    "(h : par_reduces_cd_star env e e') => ",
                    "par_reduces_cd_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_cd_star env a b) => m_star env a b) ",
                    "(fun (s : KExpr) => m_star.refl env s) ",
                    "(fun (s : KExpr) (s' : KExpr) (s'' : KExpr) ",
                    "(hstep : par_reduces_cd env s s') (_htail : par_reduces_cd_star env s' s'') ",
                    "(ih : m_star env s' s'') => ",
                    "m_star_trans env s s' s'' (par_reduces_cd_subsumes_m_star env s s' hstep) ih) ",
                    "e e' h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "par_reduces_cd_star ⊆ m_star: lift par_reduces_cd_subsumes_m_star over the union closure ",
                "(par_reduces_cd_star.rec, refl to m_star.refl, step composing the decomposed macro reduction via ",
                "m_star_trans). The HARD half of the closure-coincidence sandwich, at the closure level. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — ",
                "Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd".to_string(),
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star.rec".to_string(),
                "m_star".to_string(),
                "m_star.refl".to_string(),
                "m_star_trans".to_string(),
                "par_reduces_cd_subsumes_m_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick D6: the multi-step 3-way join witness `par_strips_witness_cd_star` — the
    /// endpoint the named β+ι+δ Church-Rosser lands at (mirror of
    /// `par_strips_witness_c_star`).
    fn add_par_strips_witness_cd_star(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive par_strips_witness_cd_star (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), par_reduces_cd_star env e1 e3 → par_reduces_cd_star env e2 e3 → par_strips_witness_cd_star env e1 e2",
            "par_strips_witness_cd_star env e1 e2 packages a common reduct e3 with par_reduces_cd_star env e1 e3 \
             and par_reduces_cd_star env e2 e3 — the MULTI-STEP 3-way (β+ι+δ) join witness the named \
             Church-Rosser par_reduces_cd_star_diamond lands at. Mirror of par_strips_witness_c_star. Part of \
             #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly).",
        )?;
        Ok(())
    }

    /// Brick D7: `par_reduces_cd_star_diamond_of_commute` — the 3-way (β+ι+δ)
    /// Church-Rosser of `par_reduces_cd_star`, MODULO the β+ι/δ commutation. Lifts
    /// both legs into `m_star` (`par_reduces_cd_star_subsumes_m_star`), confluence-
    /// joins via `mstar_confluent_of` (discharging the β+ι corner with the landed
    /// `par_reduces_c_star_diamond` + its four faithful `RecEnv` interfaces, the δ
    /// corner with the landed `delta_cong_star_diamond`, and carrying the commutation
    /// `COMM` as the SOLE bound hypothesis), then bridges each leg back
    /// (`m_star_to_cd_star`), packaging `par_strips_witness_cd_star`.
    ///
    /// The Hindley-Rosen 3-way Church-Rosser ISOLATED to exactly the commutation. The
    /// genuine named `par_reduces_cd_star_diamond` lands once `COMM` is discharged by
    /// a proven commutation.
    fn add_par_reduces_cd_star_diamond_of_commute(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_cd_star_diamond_of_commute".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) ",
                "(i1 : RecEnvReductNotRedex (red_rec env)) (i2 : RecEnvCtorNoRecMeta (red_rec env)) ",
                "(i3 : RecEnvClosed (red_rec env)) (i4 : RecEnvLiftClosed (red_rec env)) ",
                "(COMM : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
                "par_reduces_c_star (red_rec env) s u -> delta_cong_star env s v -> ",
                "par_delta_commute_witness env u v) ",
                "(e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "par_reduces_cd_star env e e1 -> par_reduces_cd_star env e e2 -> ",
                "par_strips_witness_cd_star env e1 e2"
            )
            .to_string(),
            value_src: Some(par_reduces_cd_star_diamond_of_commute_proof()),
            is_axiom: false,
            description: concat!(
                "par_reduces_cd_star_diamond_of_commute — the 3-way (β+ι+δ) Church-Rosser of ",
                "par_reduces_cd_star, MODULO the β+ι/δ commutation. Lifts both legs into m_star ",
                "(par_reduces_cd_star_subsumes_m_star), confluence-joins via mstar_confluent_of (the β+ι corner ",
                "discharged with the landed par_reduces_c_star_diamond + its four faithful RecEnv interfaces, the ",
                "δ corner with the landed delta_cong_star_diamond, the commutation COMM carried as the SOLE bound ",
                "hypothesis), then bridges each leg back (m_star_to_cd_star), packaging par_strips_witness_cd_star. ",
                "The Hindley-Rosen 3-way Church-Rosser ISOLATED to exactly the commutation; the genuine named ",
                "par_reduces_cd_star_diamond lands once COMM is discharged. DerivedProved, zero axiom_deps. Part ",
                "of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_cd_star".to_string(),
                "par_reduces_cd_star_subsumes_m_star".to_string(),
                "m_star".to_string(),
                "m_star_to_cd_star".to_string(),
                "m_star_join".to_string(),
                "m_star_join.rec".to_string(),
                "mstar_confluent_of".to_string(),
                "par_reduces_c_star_diamond".to_string(),
                "delta_cong_star_diamond".to_string(),
                "par_delta_commute_witness".to_string(),
                "par_strips_witness_cd_star".to_string(),
                "par_strips_witness_cd_star.intro".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}

/// Proof term for `par_reduces_cd_subsumes_m_star` — `par_reduces_cd.rec` with the
/// nine constructor arms. `m_star env e e'` motive.
fn par_reduces_cd_subsumes_m_star_proof() -> String {
    let motive = "(fun (a : KExpr) (b : KExpr) (_ : par_reduces_cd env a b) => m_star env a b)";
    let refl_arm = "(fun (e : KExpr) => m_star.refl env e)";
    // beta: app (lam A body) arg => instantiate body' arg'. Reduce subterms via
    // m_star_app (m_star_lam) then fire one par_reduces_c.beta (refls) as one macro step.
    let beta_fire = concat!(
        "(m_step_to_mstar env (KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
        "(m_step.par env (KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
        "(par_subsumes_par_c_star (red_rec env) (KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
        "(par_reduces_c.beta (red_rec env) A' A' body' body' arg' arg' ",
        "(par_reduces_c.refl (red_rec env) A') (par_reduces_c.refl (red_rec env) body') (par_reduces_c.refl (red_rec env) arg')))))"
    );
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_cd env A A') (_hbody : par_reduces_cd env body body') (_harg : par_reduces_cd env arg arg') ",
            "(ihA : m_star env A A') (ihbody : m_star env body body') (iharg : m_star env arg arg') => ",
            "m_star_trans env (KExpr.app (KExpr.lam A body) arg) (KExpr.app (KExpr.lam A' body') arg') (instantiate body' arg') ",
            "(m_star_app env (KExpr.lam A body) (KExpr.lam A' body') arg arg' ",
            "(m_star_lam env A A' body body' ihA ihbody) iharg) ",
            "{beta_fire})"
        ),
        beta_fire = beta_fire,
    );
    // app/lam/pi congruence arms.
    let app_arm = concat!(
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_cd env f f') (_ha : par_reduces_cd env a a') ",
        "(ihf : m_star env f f') (iha : m_star env a a') => ",
        "m_star_app env f f' a a' ihf iha)"
    );
    let lam_arm = concat!(
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_cd env ty ty') (_hbody : par_reduces_cd env body body') ",
        "(ihty : m_star env ty ty') (ihbody : m_star env body body') => ",
        "m_star_lam env ty ty' body body' ihty ihbody)"
    );
    let pi_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_cd env dom dom') (_hbody : par_reduces_cd env body body') ",
        "(ihd : m_star env dom dom') (ihbody : m_star env body body') => ",
        "m_star_pi env dom dom' body body' ihd ihbody)"
    );
    // forall_ via m_star_pi (forall_ ≡ pi reducible alias; defeq).
    let forall_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_cd env dom dom') (_hbody : par_reduces_cd env body body') ",
        "(ihd : m_star env dom dom') (ihbody : m_star env body body') => ",
        "m_star_pi env dom dom' body body' ihd ihbody)"
    );
    // let_ (ZETA): let_ ty val body => instantiate body' val' at the GENUINE 7th
    // KExpr ctor (the old app(lam) reducible alias is gone). Reduce the three slots
    // via the compound macro let congruence m_star_let, then fire one
    // par_reduces_c.let_ zeta (refls) as one macro step — the beta mechanism.
    let let_fire = concat!(
        "(m_step_to_mstar env (KExpr.let_ ty' val' body') (instantiate body' val') ",
        "(m_step.par env (KExpr.let_ ty' val' body') (instantiate body' val') ",
        "(par_subsumes_par_c_star (red_rec env) (KExpr.let_ ty' val' body') (instantiate body' val') ",
        "(par_reduces_c.let_ (red_rec env) ty' ty' val' val' body' body' ",
        "(par_reduces_c.refl (red_rec env) ty') (par_reduces_c.refl (red_rec env) val') (par_reduces_c.refl (red_rec env) body')))))"
    );
    let let_arm = format!(
        concat!(
            "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
            "(_hty : par_reduces_cd env ty ty') (_hval : par_reduces_cd env val val') (_hbody : par_reduces_cd env body body') ",
            "(ihty : m_star env ty ty') (ihval : m_star env val val') (ihbody : m_star env body body') => ",
            "m_star_trans env (KExpr.let_ ty val body) (KExpr.let_ ty' val' body') (instantiate body' val') ",
            "(m_star_let env ty ty' val val' body body' ihty ihval ihbody) ",
            "{let_fire})"
        ),
        let_fire = let_fire,
    );
    // let_cong (TRAILING congruence ctor): let_ ty val body => let_ ty' val' body' —
    // exactly the compound macro let congruence on the IHs.
    let let_cong_arm = concat!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_cd env ty ty') (_hval : par_reduces_cd env val val') (_hbody : par_reduces_cd env body body') ",
        "(ihty : m_star env ty ty') (ihval : m_star env val val') (ihbody : m_star env body body') => ",
        "m_star_let env ty ty' val val' body body' ihty ihval ihbody)"
    );
    // proj (TRAILING congruence ctor, genuine 1-slot node): the scrutinee reduces —
    // exactly the macro-star proj congruence on the IH.
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_cd env sub sub') (ihsub : m_star env sub sub') => ",
        "m_star_proj env s i sub sub' ihsub)"
    );
    // iota: one par_reduces_c.iota embed.
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hi : iota_step (red_rec env) e0 e0') => ",
        "m_step_to_mstar env e0 e0' ",
        "(m_step.par env e0 e0' ",
        "(par_subsumes_par_c_star (red_rec env) e0 e0' (par_reduces_c.iota (red_rec env) e0 e0' hi))))"
    );
    // delta: one delta_cong.here embed.
    let delta_arm = concat!(
        "(fun (e0 : KExpr) (e0' : KExpr) (hd : delta_step (red_def env) e0 e0') => ",
        "m_step_to_mstar env e0 e0' ",
        "(m_step.delta env e0 e0' ",
        "(delta_cong_subsumes_star env e0 e0' (delta_cong.here env e0 e0' hd))))"
    );
    format!(
        concat!(
            "fun (env : RedEnv) (e0 : KExpr) (e0' : KExpr) (h0 : par_reduces_cd env e0 e0') => ",
            "par_reduces_cd.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {delta_arm} {let_cong_arm} {proj_arm} ",
            "e0 e0' h0"
        ),
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        delta_arm = delta_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Proof term for `par_reduces_cd_star_diamond_of_commute` — the sandwich
/// composition.
fn par_reduces_cd_star_diamond_of_commute_proof() -> String {
    // The discharged β+ι corner: par_reduces_c_star_diamond + the four interfaces.
    let pcr = concat!(
        "(fun (s : KExpr) (u : KExpr) (v : KExpr) ",
        "(hu : par_reduces_c_star (red_rec env) s u) (hv : par_reduces_c_star (red_rec env) s v) => ",
        "par_reduces_c_star_diamond (red_rec env) s u v i1 i2 i3 i4 hu hv)"
    );
    // The discharged δ corner: delta_cong_star_diamond (no interfaces).
    let dcr = concat!(
        "(fun (s : KExpr) (u : KExpr) (v : KExpr) ",
        "(hu : delta_cong_star env s u) (hv : delta_cong_star env s v) => ",
        "delta_cong_star_diamond env s u v hu hv)"
    );
    format!(
        concat!(
            "fun (env : RedEnv) ",
            "(i1 : RecEnvReductNotRedex (red_rec env)) (i2 : RecEnvCtorNoRecMeta (red_rec env)) ",
            "(i3 : RecEnvClosed (red_rec env)) (i4 : RecEnvLiftClosed (red_rec env)) ",
            "(COMM : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
            "par_reduces_c_star (red_rec env) s u -> delta_cong_star env s v -> par_delta_commute_witness env u v) ",
            "(e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
            "(h1 : par_reduces_cd_star env e e1) (h2 : par_reduces_cd_star env e e2) => ",
            "@m_star_join.rec env e1 e2 ",
            "(fun (_w : m_star_join env e1 e2) => par_strips_witness_cd_star env e1 e2) ",
            "(fun (c : KExpr) (j1 : m_star env e1 c) (j2 : m_star env e2 c) => ",
            "par_strips_witness_cd_star.intro env e1 e2 c ",
            "(m_star_to_cd_star env e1 c j1) (m_star_to_cd_star env e2 c j2)) ",
            "(mstar_confluent_of env {pcr} {dcr} COMM e e1 e2 ",
            "(par_reduces_cd_star_subsumes_m_star env e e1 h1) ",
            "(par_reduces_cd_star_subsumes_m_star env e e2 h2))"
        ),
        pcr = pcr,
        dcr = dcr,
    )
}

#[cfg(test)]
#[path = "par_reduces_cd_hr_compose_tests.rs"]
mod par_reduces_cd_hr_compose_tests;

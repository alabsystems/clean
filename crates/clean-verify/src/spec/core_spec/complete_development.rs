// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment F+ (#2859 computational-iota/delta track): the COMPLETE DEVELOPMENT
//! `cd` for the proper parallel reduction `par_reduces_p`.
//!
//! `cd env e` contracts ALL redexes present in `e` in one shot (the Takahashi `*`
//! operation). The strong single-step diamond `par_strips_p` needs it: the iota_p
//! arm's IH-join yields a star leg, but the TRIANGLE `e ⇒_p e' → e' ⇒_p cd e` gives
//! single legs (`a ⇒_p cd e ← b`, both one step), hence the diamond.
//!
//! KEY: `cd` is STRUCTURAL (KExpr.rec), NOT strong-recursion — the iota develop is
//! `iota_reduct env (app (cd f) (cd a))` (the iota reduct of the ALREADY-developed
//! spine), so each recursive `cd` call is on a strict sub-term. cd's app arm:
//!   * the ORIGINAL `f` is a lam (beta redex present):
//!     contract `instantiate (lam-body (cd f)) (cd a)`.
//!   * else `iota_reduct env (app (cd f) (cd a)) = some r` (iota redex on the
//!     developed spine — cd preserves the recursor + ctor heads): the reduct `r`.
//!   * else: `app (cd f) (cd a)` (no top redex; subterms developed).
//! sort/bvar/const are fixed; lam/pi/forall_ recurse into the components.
//! `let_` is now a GENUINE 7th KExpr constructor (always a zeta redex, never
//! neutral): cd's let arm FIRES the top zeta on the developed components —
//! `instantiate (cd body) (cd val)` — exactly the beta arm's bare-instantiate
//! shape transplanted to the let/zeta redex.
//!
//! Parallel-iota is what makes this work: with the atomic c-iota the triangle's
//! refl case `e ⇒ cd e` would be 2-step; `iota_p` (baking in the subterm reduction)
//! makes it 1-step. See `designs/2026-06-14-computational-iota-delta-track.md` §11.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Inline `KExpr.rec` discriminator (7-ctor): non-Lam -> Nat, Lam -> Empty. Refutes
/// `KExpr.let_ .. = KExpr.lam ..` source equations now that `let_` is a genuine
/// constructor (the retired app(lam) alias let `app_ne_lam` cover them). Mirrors
/// the discrimination-lane `KEXPR_NOT_LAM_INLINE` with the trailing let_ minor.
const CD_KEXPR_NOT_LAM: &str = concat!(
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

/// Inline `KExpr.rec` discriminator (7-ctor): non-App -> Nat, App -> Empty. Refutes
/// `KExpr.let_ .. = KExpr.app ..` source equations (a genuine let is NEVER app-headed
/// — under the retired alias it literally WAS an app and fed the beta continuation).
const CD_KEXPR_NOT_APP: &str = concat!(
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

impl Specification {
    pub(super) fn add_complete_development(&mut self) -> Result<(), SpecError> {
        // opt_default o dflt: the value of o, or dflt if none. The "fire iota or keep
        // the reassembled app" combinator cd's app arm uses.
        self.add_recursive_def(
            r"def opt_default (o : OptionType KExpr) (dflt : KExpr) : KExpr := OptionType.rec KExpr (fun (_ : OptionType KExpr) => KExpr) dflt (fun (r : KExpr) => r) o",
            "opt_default o dflt = r if o = some r, else dflt. OptionType.rec on o (none -> dflt, some r -> r). \
             The cd app arm uses it: fire the iota reduct if the developed spine is a redex, else keep the \
             reassembled application. Part of #2859 (Increment F+, complete development).",
        )?;

        // kexpr_is_lam e: true iff e is a lambda. cd's beta detector (on the
        // DEVELOPED head cd f — cd preserves lam-ness).
        self.add_recursive_def(
            r"def kexpr_is_lam (e : KExpr) : Bool := KExpr.rec (fun (_ : KExpr) => Bool) (fun (n : Level) => Bool.false) (fun (i : Nat) => Bool.false) (fun (f : KExpr) (a : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (ty : KExpr) (b : KExpr) (_ : Bool) (_ : Bool) => Bool.true) (fun (ty : KExpr) (b : KExpr) (_ : Bool) (_ : Bool) => Bool.false) (fun (nm : Name) (us : ListType Level) => Bool.false) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_ : Bool) (_ : Bool) (_ : Bool) => Bool.false) (fun (s : Name) (i : Nat) (sub : KExpr) (_ : Bool) => Bool.false) (fun (v : Nat) => Bool.false) e",
            "kexpr_is_lam e = true iff e is a KExpr.lam. KExpr.rec discriminator (lam -> true, else false). \
             cd's beta detector. Part of #2859 (Increment F+, complete development).",
        )?;

        // kexpr_lam_body e: the body of a lambda (sort 0 default for non-lams — only
        // consulted when e is a lam). cd extracts the developed beta-redex body from
        // cd f (which is a lam when f is).
        self.add_recursive_def(
            r"def kexpr_lam_body (e : KExpr) : KExpr := KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort Level.zero) (fun (i : Nat) => KExpr.sort Level.zero) (fun (f : KExpr) (a : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.sort Level.zero) (fun (ty : KExpr) (b : KExpr) (_ : KExpr) (_ : KExpr) => b) (fun (ty : KExpr) (b : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.sort Level.zero) (fun (nm : Name) (us : ListType Level) => KExpr.sort Level.zero) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_ : KExpr) (_ : KExpr) (_ : KExpr) => KExpr.sort Level.zero) (fun (s : Name) (i : Nat) (sub : KExpr) (_ : KExpr) => KExpr.sort Level.zero) (fun (v : Nat) => KExpr.sort Level.zero) e",
            "kexpr_lam_body e = the body b when e = KExpr.lam ty b, else KExpr.sort 0 (default, only consulted \
             on lams). KExpr.rec projector. cd extracts the developed beta body from cd f. Part of #2859 \
             (Increment F+, complete development).",
        )?;

        // cd env e: the complete development of e (contract all present redexes,
        // develop subterms). STRUCTURAL KExpr.rec; the app arm is the redex logic.
        self.add_recursive_def(
            r"def cd (env : RecEnv) (e : KExpr) : KExpr := KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (f : KExpr) (a : KExpr) (cdf : KExpr) (cda : KExpr) => Bool.rec (fun (_ : Bool) => KExpr) (opt_default (iota_reduct env (KExpr.app cdf cda)) (KExpr.app cdf cda)) (instantiate (kexpr_lam_body cdf) cda) (kexpr_is_lam f)) (fun (ty : KExpr) (b : KExpr) (cdty : KExpr) (cdb : KExpr) => KExpr.lam cdty cdb) (fun (ty : KExpr) (b : KExpr) (cdty : KExpr) (cdb : KExpr) => KExpr.pi cdty cdb) (fun (nm : Name) (us : ListType Level) => KExpr.const nm us) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (cdty : KExpr) (cdval : KExpr) (cdbody : KExpr) => instantiate cdbody cdval) (fun (s : Name) (i : Nat) (sub : KExpr) (cdsub : KExpr) => KExpr.proj s i cdsub) (fun (v : Nat) => KExpr.lit v) e",
            "The complete development cd env e: contract every redex PRESENT in e (not ones created by \
             developing subterms) and develop the subterms, in one shot (Takahashi *). STRUCTURAL KExpr.rec \
             (env fixed). app arm: if the ORIGINAL head f is a lam (beta redex present) -> beta-contract \
             instantiate (kexpr_lam_body (cd f)) (cd a) (kexpr_lam_body (cd f) = cd of f's body); elif the \
             developed spine (app (cd f)(cd a)) is an iota redex (equiv. to the original by head preservation) \
             -> its reduct (opt_default + iota_reduct); else the reassembled app (cd f)(cd a). sort/bvar/const \
             fixed; lam/pi recurse; forall_ via its pi alias. let_ (genuine 7th ctor, always a zeta redex) \
             FIRES the top zeta on the developed components: instantiate (cd body)(cd val) — the beta arm's \
             shape transplanted to the let/zeta redex. The triangle (e =>_p e' -> \
             e' =>_p cd e) gives the strong single-step diamond. Part of #2859 (Increment F+, complete development).",
        )?;

        self.add_cd_unfold()?;
        self.add_par_reduces_p_lam_inv()?;
        self.add_dev0()?;

        Ok(())
    }

    /// The LITERAL-scrutinee complete development `dev0` (blueprint Basic.lean:305,
    /// the anti-`cd` developer). Identical to `cd` in every arm EXCEPT the iota
    /// decision: `cd` fires iota when the *developed* spine `app (cd f)(cd a)` is a
    /// redex (`iota_reduct env (app cdf cda)`), which LOOKS AHEAD through the
    /// scrutinee — developing the major argument can turn a non-redex into a redex,
    /// so `cd e` is not single-step-reachable from a literal-redex source, and the
    /// Takahashi triangle's iota arm WALLS (design §18, kernel-REFUTED: `cdr ≠ cd x`,
    /// needs the circular `cd`-preservation-under-reduction). `dev0` instead fires
    /// iota only when the *literal* source spine `app f a` is already a redex
    /// (`iota_reduct env (app f a)`), reassembling the reduct from the DEVELOPED
    /// components (`iota_reduct env (app (dev0 f)(dev0 a))` — the same developed
    /// output as `cd`, but GATED on the literal redex status). This matches the
    /// blueprint `dev0` exactly: decide on the literal scrutinee, develop the
    /// components — no look-ahead, so `par0_triangle` has no iota wall.
    ///
    /// The beta arm is UNCHANGED from `cd` (`kexpr_is_lam f` already inspects the
    /// LITERAL head `f`, not a developed one — beta never had the look-ahead bug;
    /// only iota did).
    fn add_dev0(&mut self) -> Result<(), SpecError> {
        // dev0 env e: literal-scrutinee complete development. STRUCTURAL KExpr.rec.
        // app arm: beta branch (kexpr_is_lam f) identical to cd; the else branch
        // gates the developed-spine iota reduct on the LITERAL redex test via an
        // OptionType.rec on `iota_reduct env (app f a)` (the LITERAL spine): the
        // none branch keeps the reassembled `app df da` (NOT a present redex), the
        // some branch re-fires on the DEVELOPED spine (head/major const preserved by
        // development, so the developed spine is also a redex) via opt_default. This
        // is exactly cd's iota output, but GATED on the literal (not developed) test.
        self.add_recursive_def(
            r"def dev0 (env : RecEnv) (e : KExpr) : KExpr := KExpr.rec (fun (_ : KExpr) => KExpr) (fun (n : Level) => KExpr.sort n) (fun (i : Nat) => KExpr.bvar i) (fun (f : KExpr) (a : KExpr) (df : KExpr) (da : KExpr) => Bool.rec (fun (_ : Bool) => KExpr) (OptionType.rec KExpr (fun (_ : OptionType KExpr) => KExpr) (KExpr.app df da) (fun (_ : KExpr) => opt_default (iota_reduct env (KExpr.app df da)) (KExpr.app df da)) (iota_reduct env (KExpr.app f a))) (instantiate (kexpr_lam_body df) da) (kexpr_is_lam f)) (fun (ty : KExpr) (b : KExpr) (dty : KExpr) (db : KExpr) => KExpr.lam dty db) (fun (ty : KExpr) (b : KExpr) (dty : KExpr) (db : KExpr) => KExpr.pi dty db) (fun (nm : Name) (us : ListType Level) => KExpr.const nm us) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (dty : KExpr) (dval : KExpr) (dbody : KExpr) => instantiate dbody dval) (fun (s : Name) (i : Nat) (sub : KExpr) (dsub : KExpr) => KExpr.proj s i dsub) (fun (v : Nat) => KExpr.lit v) e",
            "The LITERAL-scrutinee complete development dev0 env e (blueprint dev0): contract every redex \
             PRESENT in the LITERAL e and develop subterms, in one shot. STRUCTURAL KExpr.rec. app arm: if the \
             ORIGINAL head f is a lam (beta present) -> instantiate (kexpr_lam_body (dev0 f)) (dev0 a) (same as \
             cd); elif the LITERAL spine (app f a) is an iota redex (OptionType.rec on iota_reduct env (app f \
             a)) -> the developed reduct (opt_default (iota_reduct env (app (dev0 f)(dev0 a)))); else the \
             reassembled app (dev0 f)(dev0 a). The ONLY difference vs cd is the iota GATE: cd tests the \
             DEVELOPED spine (look-ahead, design §18 wall), dev0 tests the LITERAL spine (no look-ahead). \
             sort/bvar/const fixed; lam/pi recurse. let_ (genuine 7th ctor, always a zeta redex — a let is \
             never an iota/delta redex, so no gate is involved) fires the top zeta on the developed \
             components: instantiate (dev0 body)(dev0 val), same as cd. Part of #2859 (Increment F+, \
             literal-scrutinee developer).",
        )?;

        self.add_dev0_unfold()?;

        Ok(())
    }

    /// The computational unfold lemmas for `dev0` (all `Eq.refl`, mirroring the `cd`
    /// unfolds): `dev0_lam` / `dev0_pi` (binder arms), `dev0_app` (the raw Bool.rec
    /// form), `dev0_app_lam` (the resolved beta branch). These name the development
    /// targets the `dev0_refl` / `dev0_triangle` arms rewrite against.
    fn add_dev0_unfold(&mut self) -> Result<(), SpecError> {
        // dev0_lam / dev0_pi: binder unfold dev0 env (HEAD ty b) = HEAD (dev0 ty)(dev0 b) — refl.
        for (name, head) in [("dev0_lam", "KExpr.lam"), ("dev0_pi", "KExpr.pi")] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "forall (env : RecEnv) (ty : KExpr) (b : KExpr), \
                     Eq KExpr (dev0 env ({head} ty b)) ({head} (dev0 env ty) (dev0 env b))"
                ),
                value_src: Some(format!(
                    "fun (env : RecEnv) (ty : KExpr) (b : KExpr) => \
                     Eq.refl KExpr (dev0 env ({head} ty b))"
                )),
                is_axiom: false,
                description: format!(
                    "dev0 unfold for {head}: dev0 env ({head} ty b) = {head} (dev0 env ty)(dev0 env b). \
                     Reflexivity (the kernel computes the KExpr.rec binder arm). Part of #2859 (Increment F+)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "dev0".to_string(),
                    "Eq.refl".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // dev0_let: the let/zeta arm unfold (clone of dev0_app_lam's resolved-redex
        // shape — a let_ is ALWAYS a zeta redex, no gate). dev0 env (let_ ty val body)
        // = instantiate (dev0 body)(dev0 val). Reflexivity.
        self.add_definition(SpecDefinition {
            name: "dev0_let".to_string(),
            type_src: "forall (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr), \
                 Eq KExpr (dev0 env (KExpr.let_ ty val body)) (instantiate (dev0 env body) (dev0 env val))"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr) => \
                 Eq.refl KExpr (dev0 env (KExpr.let_ ty val body))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "dev0 unfold for the genuine let_ ctor (zeta redex always present, no gate): dev0 env (let_ ty val body) = instantiate (dev0 env body)(dev0 env val). Reflexivity — the beta-branch (dev0_app_lam) shape transplanted to the let/zeta redex. Part of #2859 (let-promotion B4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "dev0".to_string(),
                "instantiate".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // dev0_app: the raw app unfold (stuck on kexpr_is_lam f). dev0 env (app f a) =
        // Bool.rec ... (the LITERAL-gated OptionType.rec on iota_reduct env (app f a))
        // (instantiate (kexpr_lam_body (dev0 f)) (dev0 a)) (kexpr_is_lam f). Reflexivity.
        self.add_definition(SpecDefinition {
            name: "dev0_app".to_string(),
            type_src: "forall (env : RecEnv) (f : KExpr) (a : KExpr), \
                 Eq KExpr (dev0 env (KExpr.app f a)) \
                 (Bool.rec (fun (_ : Bool) => KExpr) \
                 (OptionType.rec KExpr (fun (_ : OptionType KExpr) => KExpr) \
                 (KExpr.app (dev0 env f) (dev0 env a)) \
                 (fun (_ : KExpr) => opt_default (iota_reduct env (KExpr.app (dev0 env f) (dev0 env a))) (KExpr.app (dev0 env f) (dev0 env a))) \
                 (iota_reduct env (KExpr.app f a))) \
                 (instantiate (kexpr_lam_body (dev0 env f)) (dev0 env a)) \
                 (kexpr_is_lam f))"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (f : KExpr) (a : KExpr) => \
                 Eq.refl KExpr (dev0 env (KExpr.app f a))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "dev0 unfold for app (raw, stuck on kexpr_is_lam f): dev0 env (app f a) = Bool.rec ... (kexpr_is_lam f), with the LITERAL-gated OptionType.rec on iota_reduct env (app f a) in the false branch. Reflexivity. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "dev0".to_string(),
                "Bool.rec".to_string(),
                "OptionType.rec".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "instantiate".to_string(),
                "kexpr_lam_body".to_string(),
                "kexpr_is_lam".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // dev0_app_lam: the resolved beta branch (head is a syntactic lam, identical to
        // cd's beta arm). dev0 env (app (lam A b) a) = instantiate (dev0 b)(dev0 a). Refl.
        self.add_definition(SpecDefinition {
            name: "dev0_app_lam".to_string(),
            type_src: "forall (env : RecEnv) (A : KExpr) (b : KExpr) (a : KExpr), \
                 Eq KExpr (dev0 env (KExpr.app (KExpr.lam A b) a)) (instantiate (dev0 env b) (dev0 env a))"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (A : KExpr) (b : KExpr) (a : KExpr) => \
                 Eq.refl KExpr (dev0 env (KExpr.app (KExpr.lam A b) a))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "dev0 unfold for an app whose head is a syntactic lam (beta redex present, same as cd): dev0 env (app (lam A b) a) = instantiate (dev0 env b)(dev0 env a). Reflexivity. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "dev0".to_string(),
                "instantiate".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// L1a (#2859 Increment F+): the lam-headed inversion for `par_reduces_p`
    /// (`par_reduces_p_lam_inv`) and its head-shape prerequisite
    /// (`par_reduces_p_lam_head_none`). Template: `par_reduces_c_lam_inv`
    /// (par_reduces_c.rs ~line 3109). The genuine new content vs. the c-mirror is the
    /// PARALLEL-iota arm: `par_reduces_p.iota_p` fires on the REDUCED redex `e2` (the
    /// premise `e0 ⇒_p e2`), NOT on the source `e0`. So the binder-head-discharge
    /// (`iota_step_head_none_absurd_type`) cannot be aimed at the lam head directly —
    /// it must be aimed at `e2`. We first learn `e2` is head-none from the recursive
    /// premise via `par_reduces_p_lam_head_none` (a lam par-reduces only to a head-none
    /// term), then discharge the iota on `e2`.
    fn add_par_reduces_p_lam_inv(&mut self) -> Result<(), SpecError> {
        // par_reduces_p_lam_head_none: a lam-headed source par-reduces only to a
        // par-reduct t cannot itself be an iota redex (a lam par-reduces only to a
        // lam, which is binder-headed, never a const-recursor redex). Type-valued
        // (C : Type) so the par_reduces_p.rec motive lands in Type — this both gives
        // the discharge par_reduces_p_lam_inv's iota arm needs (the iota there fires on
        // the REDUCED redex t = e2, a par-reduct of the lam) and keeps the recursion
        // Type-valued. The iota_p arm is the crux: it discharges via its OWN IH applied
        // to the constructor's FIRE premise (e2 ⇒_p e2'' with iota_step e2'' r0; the IH
        // says e2'' — itself a par-reduct of the lam — is not a redex, contradicting
        // that fire), so the new outer iota on r0 is irrelevant.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_lam_reduct_not_redex".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (r : KExpr) (C : Type), ",
                "par_reduces_p env (KExpr.lam ty body) t -> ",
                "iota_step env t r -> C"
            )
            .to_string(),
            value_src: Some(par_reduces_p_lam_reduct_not_redex_proof()),
            is_axiom: false,
            description: concat!(
                "L1a prerequisite (#2859 Increment F+): a par-reduct of a lam is never an iota redex. From ",
                "par_reduces_p env (lam ty body) t and iota_step env t r, derive any C. Type-valued (C : Type), ",
                "so the par_reduces_p.rec motive lands in Type. par_reduces_p.rec with a source-equation motive ",
                "universalizing the new redex (r, C): refl/lam arms have a binder-headed reduct (lam), so the ",
                "iota on it is absurd via iota_step_head_none_absurd_type; beta/app arms are app-headed ",
                "(app_ne_lam), pi/forall_ pi-headed (pi_ne_lam), let_/let_cong let-headed (KExpr let/lam ",
                "discrimination — a genuine let is never a lam); the iota_p arm discharges via its OWN IH applied ",
                "to the constructor's fire premise (the reduced sub-redex is again a par-reduct of the lam, so ",
                "not a redex). DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "instantiate".to_string(),
                "KExpr.rec".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_lam_inv: from par_reduces_p env (lam ty body) t recover
        // t = lam ty' body' with ty ⇒_p ty' and body ⇒_p body'. CPS form (mirror of
        // par_reduces_c_lam_inv). The iota_p arm: the iota fires on the REDUCED redex
        // e2 (premise e0 ⇒_p e2, e0 = lam ty body), discharged via
        // par_reduces_p_lam_head_none on the transported premise (e2 head-none) +
        // iota_step_head_none_absurd_type.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_lam_inv".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type), ",
                "par_reduces_p env (KExpr.lam ty body) t -> ",
                "(forall (ty' : KExpr) (body' : KExpr), ",
                "par_reduces_p env ty ty' -> par_reduces_p env body body' -> ",
                "C (KExpr.lam ty' body')) -> ",
                "C t"
            )
            .to_string(),
            value_src: Some(par_reduces_p_lam_inv_proof()),
            is_axiom: false,
            description: concat!(
                "L1a (#2859 Increment F+): shape-recovery (inversion) for a lam-headed par_reduces_p — from ",
                "par_reduces_p env (lam ty body) t recover t = lam ty' body' with ty ⇒_p ty' and body ⇒_p ",
                "body'. Mirror of par_reduces_c_lam_inv: refl folds in reflexive sub-derivations; the lam arm ",
                "is the genuine congruence; beta/app are app-headed (app_ne_lam), pi/forall_ pi-headed ",
                "(pi_ne_lam), let_/let_cong let-headed (KExpr let/lam discrimination). The genuine-new ",
                "PARALLEL-iota arm: the iota fires on the REDUCED redex e2 (not ",
                "the lam source e0), so it is discharged by learning e2 is head-none — the recursive premise ",
                "e0 ⇒_p e2 transported to (lam ty body) ⇒_p e2 is fed to par_reduces_p_lam_head_none, then ",
                "iota_step_head_none_absurd_type closes the fired iota on e2. CPS form. DerivedProved, zero ",
                "axiom_deps. Part of #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p_lam_reduct_not_redex".to_string(),
                "iota_step".to_string(),
                "iota_step_head_none_absurd_type".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "app_ne_lam".to_string(),
                "pi_ne_lam".to_string(),
                "instantiate".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_cd_refl()?;

        Ok(())
    }

    /// L1b (#2859 Increment F+): `cd_refl` — every term parallel-reduces to its
    /// complete development (`par_reduces_p env e (cd env e)`). Structural induction on
    /// `e` (`KExpr.rec`) aligning each `cd` branch with a `par_reduces_p` constructor.
    /// The app arm is the fiddly one: `kexpr_lam_cases f` splits the beta branch (head a
    /// syntactic lam — `cd_app_lam` + a `par_reduces_p.beta`, with the body/dom
    /// component reductions recovered from the f-IH via `par_reduces_p_lam_inv` (L1a))
    /// from the iota/app branch (`cd_app` + `hfalse` transports `cd (app f a)` to the
    /// `opt_default (iota_reduct …)` form, then an OptionType convoy picks the iota_p
    /// firing branch vs the plain app congruence).
    fn add_cd_refl(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "cd_refl".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr), ",
                "par_reduces_p env e (cd env e)"
            )
            .to_string(),
            value_src: Some(cd_refl_proof()),
            is_axiom: false,
            description: concat!(
                "L1b (#2859 Increment F+): every term parallel-reduces to its complete development — ",
                "par_reduces_p env e (cd env e). Structural KExpr.rec on e: sort/bvar/const arms are refl; ",
                "lam/pi arms are par_reduces_p.lam/.pi on the component IHs (via cd_lam/cd_pi). The app arm ",
                "splits on kexpr_lam_cases f: (1) f = lam A b0 (beta present) — cd (app (lam A b0) a) = ",
                "instantiate (cd b0)(cd a) (cd_app_lam), proved by par_reduces_p.beta with the A/b0 component ",
                "reductions recovered from the f-IH (par_reduces_p env (lam A b0)(cd (lam A b0))) via ",
                "par_reduces_p_lam_inv; (2) kexpr_is_lam f = false — cd (app f a) transports (cd_app + hfalse) ",
                "to opt_default (iota_reduct env (app (cd f)(cd a))) (app (cd f)(cd a)), then an OptionType ",
                "convoy: the none branch is par_reduces_p.app on the IHs, the some-r branch is ",
                "par_reduces_p.iota_p (app f a)(app (cd f)(cd a)) r (app-cong on IHs)(the some-equation = ",
                "iota_step). The let_ arm (genuine 7th ctor) fires the top zeta: cd (let_ ty val body) = ",
                "instantiate (cd body)(cd val) (cd_let), proved by par_reduces_p.let_ on the three IHs — the ",
                "beta-branch shape with no inversion needed. DerivedProved, zero axiom_deps. Part of #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p.beta".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.lam".to_string(),
                "par_reduces_p.pi".to_string(),
                "par_reduces_p.iota_p".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_p_lam_inv".to_string(),
                "cd".to_string(),
                "cd_lam".to_string(),
                "cd_pi".to_string(),
                "cd_let".to_string(),
                "cd_app".to_string(),
                "cd_app_lam".to_string(),
                "kexpr_lam_cases".to_string(),
                "kexpr_is_lam".to_string(),
                "kexpr_lam_body".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "iota_step".to_string(),
                "instantiate".to_string(),
                "KExpr.rec".to_string(),
                "Bool.rec".to_string(),
                "OptionType.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_par_reduces_p_reduct_cong()?;

        Ok(())
    }

    /// L2 (#2859 Increment F+, confluence core): the iota_p REDUCT congruence —
    /// computational core `par_reduces_p_reduct_cong_spine`.
    ///
    /// `par_reduces_p_reduct_cong_spine` is the STRUCTURAL-args reduct congruence
    /// (design §11: "the spine segments of e2 par-reduce to m's → apply_spine_par_p").
    /// It takes the iota-redex boundary data (`meta`/`rule`) and the two spine
    /// congruences as EXPLICIT hypotheses — the whole-app spine congruence
    /// `kapp_args (app f a) ⇒_p_list kapp_args (app f' a')` and the major's own
    /// `kapp_args major ⇒_p_list kapp_args a'` — and proves that the two iota
    /// reducts (the `(app f a)`-side reduct over the generic `major` and the
    /// `(app f' a')`-side reduct over `a'`) par-reduce. The pure 3-layer
    /// `apply_spine_par_p` assembly, a direct c→p port of `par_reduces_c_reduct_cong`'s
    /// body with the two `par_reduces_c_spine_cong` calls replaced by the hypotheses
    /// (the c-spine_cong's not-redex guard does NOT port — design §11 — so the spine
    /// congruence is supplied, not derived here).
    fn add_par_reduces_p_reduct_cong(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_reduct_cong_spine".to_string(),
            type_src: par_reduces_p_reduct_cong_spine_type(),
            value_src: Some(par_reduces_p_reduct_cong_spine_proof()),
            is_axiom: false,
            description: concat!(
                "L2 core (#2859 Increment F+): the STRUCTURAL-args iota reduct congruence for par_reduces_p. ",
                "Given the iota-redex boundary (meta, rule) and the two spine congruences as hypotheses — the ",
                "whole-app kapp_args (app f a) ⇒_p_list kapp_args (app f' a') and the major's own kapp_args ",
                "major ⇒_p_list kapp_args a' (with major = a) — the (app f a)-side iota reduct (over the generic ",
                "major) par-reduces to the (app f' a')-side reduct (over a'). The pure 3-layer apply_spine_par_p ",
                "assembly: outer (extras) + prefix layers via the whole-app spine congruence ",
                "(list_drop_par_p / list_take_par_p), middle (fields) layer via the major's own spine congruence ",
                "(a'-side drop-index rewritten by length stability par_reduces_p_list_length_eq). c→p port of ",
                "par_reduces_c_reduct_cong's body with the c-spine_cong calls replaced by hypotheses (the c ",
                "not-redex guard does NOT port — design §11). DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list_length_eq".to_string(),
                "apply_spine_par_p".to_string(),
                "list_drop_par_p".to_string(),
                "list_take_par_p".to_string(),
                "apply_spine".to_string(),
                "list_drop".to_string(),
                "list_take".to_string(),
                "kapp_args".to_string(),
                "list_length".to_string(),
                "recrule_rhs".to_string(),
                "recrule_num_fields".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_iota_redex_to_reduct: an iota redex par-reduces to its
        // reduct in ONE par_reduces_p step. The refl-case content of design §11's
        // par_reduces_p_iota_redex_cong: iota_p with a reflexive subterm-reduction
        // premise (e ⇒_p e via refl) then the fire. The parallel-iota relation makes
        // this 1-step (the atomic par_reduces_c needs the same but its diamond stays
        // star). Consumed by the iota_p arm of cd_triangle and the redex_cong refl arm.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_iota_redex_to_reduct".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (r : KExpr), ",
                "iota_step env e r -> par_reduces_p env e r"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (r : KExpr) (hi : iota_step env e r) => ",
                    "par_reduces_p.iota_p env e e r (par_reduces_p.refl env e) hi"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "An iota redex par-reduces to its reduct in ONE par_reduces_p step (the refl-case content of ",
                "design §11's par_reduces_p_iota_redex_cong): par_reduces_p.iota_p with a reflexive ",
                "subterm-reduction premise (e ⇒_p e via refl) then the fired iota. The parallel-iota relation ",
                "makes this 1-step (par_reduces_c needs the same shape but only yields a star diamond). ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment F+, confluence core)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.refl".to_string(),
                "par_reduces_p.iota_p".to_string(),
                "iota_step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_reduct_cong_over: the OVER-APPLICATION arm of the iota
        // reduct congruence (design §15(ii); the residual kcong-sub over-app gap).
        // When (app f a) is an OVER-APPLIED iota redex — the major sits strictly
        // inside f's spine, so f is ITSELF a redex (iota_reduct env f = some f1) —
        // the over-application identity (iota_reduct_app_some) makes the OUTER
        // reduct literally the inner reduct re-applied: iota_reduct env (app f a) =
        // some (app f1 a). Symmetrically iota_reduct env (app f' a') = some (app
        // f1' a'). So given the INNER reduct congruence f1 ⇒_p f1' and a ⇒_p a',
        // the two outer reducts par-reduce by a single par_reduces_p.app congruence,
        // transported onto the actual iota_reduct outputs e1 / m. The c→p analogue
        // of the c-side over-application identity (iota_reduct_app_some,
        // iota_core.rs); the over-application companion of the boundary-case
        // par_reduces_p_reduct_cong_spine.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_reduct_cong_over".to_string(),
            type_src: par_reduces_p_reduct_cong_over_type(),
            value_src: Some(par_reduces_p_reduct_cong_over_proof()),
            is_axiom: false,
            description: concat!(
                "L2 over-application arm (#2859 Increment F+, design §15(ii)): the OVER-APPLICATION iota reduct ",
                "congruence for par_reduces_p. When (app f a) is an over-applied iota redex — the major sits ",
                "strictly inside f's spine, so f is itself a redex (iota_reduct env f = some f1) — the ",
                "over-application identity iota_reduct_app_some makes the outer reduct literally the inner reduct ",
                "re-applied: iota_reduct env (app f a) = some (app f1 a), and symmetrically iota_reduct env (app ",
                "f' a') = some (app f1' a'). Given the INNER reduct congruence f1 ⇒_p f1' and a ⇒_p a', the two ",
                "actual outer reducts e1 / m par-reduce: iota_reduct_app_some on each side + option_some_inj pin ",
                "e1 = app f1 a and m = app f1' a', then a single par_reduces_p.app congruence transported onto e1 ",
                "/ m by Eq.substType. The c→p analogue of the c-side over-application identity iota_reduct_app_some ",
                "(iota_core.rs); the over-application companion of the boundary-case par_reduces_p_reduct_cong_spine. ",
                "Completes the over-application case of par_reduces_p_reduct_cong for the kcong-sub arm. Does NOT ",
                "by itself close cd_triangle (the kbeta-sub / kiota-sub wall, design §14, stays open). ",
                "DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.app".to_string(),
                "iota_reduct".to_string(),
                "iota_reduct_app_some".to_string(),
                "option_some_inj".to_string(),
                "Eq.substType".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // The below-boundary + no-recmeta spine-congruence bricks (and the full
        // assembly bundle) must be registered BEFORE the assembled
        // par_reduces_p_reduct_cong consumes them.
        self.add_below_boundary_bricks()?;
        self.add_par_reduces_p_spine_cong_below_boundary()?;
        self.add_par_reduces_p_reduct_cong_full()?;

        // par_reduces_p_reduct_cong — the ASSEMBLED minimal (LEFT-leg) reduct
        // congruence (#2859 Increment F++ keystone). The p-side analogue of the c-side
        // par_reduces_c_reduct_cong (D.3, par_reduces_c.rs:2400): given the boundary-
        // inverter witnesses for an iota redex (app f a) (recname/meta/major/cname/rule,
        // the five lookups + reduct identity h5r + boundary identity hbnd : major = a +
        // index identity hidx : major_idx = len(kapp_args f)), the originals (f ⇒_p f',
        // a ⇒_p a'), and the SHARPENED disjointness interface RecEnvCtorNoRecMeta, it
        // produces par_reduces_p e1 reduct_m (the (app f a)-side reduct e1 par-reduces to
        // the (app f' a')-side reduct reduct_m). Builds the two spine congruences and
        // feeds par_reduces_p_reduct_cong_spine (the apply_spine assembly):
        //   * f-spine (RECURSOR head): par_reduces_p_spine_cong_below_boundary (head f =
        //     some recname, recmeta_for recname = some meta = h2, and the BELOW-BOUNDARY
        //     guard Le (len(kapp_args f)) major_idx — reflexive in the minimal case since
        //     hidx : major_idx = len(kapp_args f)). Its iota_p arm discharges via the
        //     arithmetic absurdity (iota_step_below_boundary_absurd), NO interface needed.
        //   * major/a-spine (CONSTRUCTOR head): par_reduces_p_spine_cong_no_recmeta (head
        //     a = some cname, recmeta_for cname = none from the interface projector
        //     recenv_ctor_no_recmeta_cname). Its iota_p arm fires on the REDUCED premise,
        //     so it CANNOT be guarded by a source iota_reduct = none (design §11) — this
        //     is precisely why the recmeta_for = none interface is required (the c→p
        //     divergence the handover diagnosed). Transported source kapp_args a ->
        //     kapp_args major via Eq.symm hbnd.
        // Recover e1 = R_fa from h5r (option_some_inj) and transport the source. The
        // unconditional (modulo the faithful interface) c→p port of D.3; the c not-redex
        // guard is replaced by the below-boundary arithmetic (f) + RecEnvCtorNoRecMeta (a).
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_reduct_cong".to_string(),
            type_src: par_reduces_p_reduct_cong_type(),
            value_src: Some(par_reduces_p_reduct_cong_proof()),
            is_axiom: false,
            description: concat!(
                "The ASSEMBLED minimal (LEFT-leg) reduct congruence for par_reduces_p (#2859 Increment F++ ",
                "keystone): the p-side analogue of the c-side par_reduces_c_reduct_cong (D.3). Given the boundary-",
                "inverter witnesses for an iota redex (app f a) (recname/meta/major/cname/rule, the five lookups + ",
                "reduct identity h5r + hbnd : major = a + hidx : major_idx = len(kapp_args f)), the originals ",
                "(f ⇒_p f', a ⇒_p a'), and the sharpened disjointness interface RecEnvCtorNoRecMeta, it produces ",
                "par_reduces_p e1 reduct_m. Builds the f-spine congruence via par_reduces_p_spine_cong_below_boundary ",
                "(recursor head; below-boundary guard reflexive via hidx; iota_p arm discharged by arithmetic, NO ",
                "interface) and the major/a-spine congruence via par_reduces_p_spine_cong_no_recmeta (constructor head; ",
                "recmeta_for cname = none from recenv_ctor_no_recmeta_cname — needed because the p-side iota_p fires on ",
                "the REDUCED premise, design §11), then feeds par_reduces_p_reduct_cong_spine (the apply_spine assembly). ",
                "Recovers e1 = R_fa from h5r (option_some_inj) and transports the source. The unconditional-modulo-the-",
                "faithful-interface c→p port of D.3. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p_reduct_cong_spine".to_string(),
                "par_reduces_p_spine_cong_below_boundary".to_string(),
                "par_reduces_p_spine_cong_no_recmeta".to_string(),
                "recenv_ctor_no_recmeta_cname".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "kapp_args_par_p".to_string(),
                "par_reduces_p_list".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "kapp_args".to_string(),
                "list_length".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "option_some_inj".to_string(),
                "Le".to_string(),
                "Le.refl".to_string(),
                "Eq.subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_app_redex — the p-side (iota,app) minimal-join reduct
        // RECONSTRUCTION (the p-side analogue of the c-side iota_reduct_par_app_redex).
        // Given the boundary-inverter witnesses for an iota redex (app f a) + the
        // sharpened disjointness interface + the originals f ⇒_p f' / a ⇒_p a', it
        // delivers iota_reduct env (app f' a') = some reduct_m (the a'-side reduct).
        // Reconstructs the five (app f' a')-side lookups from the boundary witnesses + the
        // par steps (hL1 head via par_reduces_p_preserves_head_const_below_boundary; hL3
        // major-at-boundary via list_head_drop_len_append + length stability; hL4 head a'
        // via par_reduces_p_preserves_head_const_no_recmeta + recenv_ctor_no_recmeta_cname),
        // then feeds iota_reduct_par_app_recon (par_reduces_c-free — reused verbatim).
        // With par_reduces_p_reduct_cong's LEFT leg + iota_step_deterministic, this pins
        // the GIVEN opaque (app f' a')-reduct to reduct_m (the RIGHT leg of the minimal join).
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_app_redex".to_string(),
            type_src: par_reduces_p_app_redex_type(),
            value_src: Some(par_reduces_p_app_redex_proof()),
            is_axiom: false,
            description: concat!(
                "The p-side (iota,app) minimal-join reduct RECONSTRUCTION (#2859 Increment F++): the p-side ",
                "analogue of the c-side iota_reduct_par_app_redex. Given the boundary-inverter witnesses for an ",
                "iota redex (app f a) (head/meta/major/cname/rule + hbnd : major = a + hidx : major_idx = ",
                "len(kapp_args f)), the sharpened disjointness interface RecEnvCtorNoRecMeta, and the originals ",
                "f ⇒_p f' / a ⇒_p a', it delivers iota_reduct env (app f' a') = some reduct_m (the a'-side reduct). ",
                "Reconstructs the five (app f' a')-side lookups: hL1 head f' = some recname via ",
                "par_reduces_p_preserves_head_const_below_boundary (below-boundary guard reflexive via hidx); hL3 ",
                "major-at-boundary via list_head_drop_len_append + length stability (par_reduces_p_list_length_eq); ",
                "hL4 head a' = some cname via par_reduces_p_preserves_head_const_no_recmeta (no-recmeta guard from ",
                "recenv_ctor_no_recmeta_cname); h2/h5 reused; then feeds iota_reduct_par_app_recon (which is ",
                "par_reduces_c-free — reused verbatim across the c/p tracks). The RIGHT leg of the (iota,app) ",
                "minimal join: with par_reduces_p_reduct_cong's LEFT leg + iota_step_deterministic, pins the GIVEN ",
                "opaque (app f' a')-reduct to reduct_m. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "iota_reduct".to_string(),
                "iota_reduct_par_app_recon".to_string(),
                "par_reduces_p_spine_cong_below_boundary".to_string(),
                "par_reduces_p_preserves_head_const_below_boundary".to_string(),
                "par_reduces_p_preserves_head_const_no_recmeta".to_string(),
                "par_reduces_p_list_length_eq".to_string(),
                "recenv_ctor_no_recmeta_cname".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "list_head_drop_len_append".to_string(),
                "kapp_args_app".to_string(),
                "kapp_fn_app".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "list_head".to_string(),
                "list_drop".to_string(),
                "list_append".to_string(),
                "list_length".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "Le".to_string(),
                "Le.refl".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_app_reduct_cong_minimal — the MINIMAL-case (f not a redex) `happ`
        // congruence: given iota_reduct env f = none, the disjointness interface, the
        // originals f ⇒_p f' / a ⇒_p a', and BOTH endpoints as iota redexes (the GIVEN
        // iota_step (app f a) r0 and iota_step (app f' a') rm0), the two reducts join in
        // par_reduces_p_star. Invert (app f a) via iota_reduct_app_minimal_boundary_idx_type
        // (Type-valued C = the star goal); the LEFT leg r0 ⇒_p reduct_m is
        // par_reduces_p_reduct_cong; the RIGHT leg pins rm0 = reduct_m by reconstructing
        // iota_reduct (app f' a') = some reduct_m (par_reduces_p_app_redex) +
        // iota_step_deterministic against the GIVEN rm0; transport + subsume to star. The
        // boundary-case half of the keystone's app arm; the over-application case (f itself
        // a redex) is dispatched by the keystone's outer fuel IH, NOT this lemma.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_app_reduct_cong_minimal".to_string(),
            type_src: par_reduces_p_app_reduct_cong_minimal_type(),
            value_src: Some(par_reduces_p_app_reduct_cong_minimal_proof()),
            is_axiom: false,
            description: concat!(
                "The MINIMAL-case (f not a redex) symmetric app reduct congruence (#2859 Increment F++ keystone): ",
                "given iota_reduct env f = none, the sharpened disjointness interface RecEnvCtorNoRecMeta, the ",
                "originals f ⇒_p f' / a ⇒_p a', and BOTH endpoints as iota redexes (iota_step (app f a) r0, ",
                "iota_step (app f' a') rm0), the two reducts join in par_reduces_p_star. Inverts (app f a) via ",
                "iota_reduct_app_minimal_boundary_idx_type (Type-valued continuation); the LEFT leg r0 ⇒_p reduct_m ",
                "is par_reduces_p_reduct_cong (recovers r0 = R_fa from h5r); the RIGHT leg pins rm0 = reduct_m by ",
                "reconstructing iota_reduct (app f' a') = some reduct_m (par_reduces_p_app_redex) + ",
                "iota_step_deterministic against the GIVEN rm0; transport r0 ⇒_p reduct_m onto r0 ⇒_p rm0 and ",
                "subsume to star (par_subsumes_par_p_star). The boundary-case half of the keystone's app arm — the ",
                "over-application case (f itself a redex) routes through the keystone's outer fuel IH, NOT this ",
                "lemma. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p_star".to_string(),
                "par_subsumes_par_p_star".to_string(),
                "par_reduces_p_reduct_cong".to_string(),
                "par_reduces_p_app_redex".to_string(),
                "iota_reduct_app_minimal_boundary_idx_type".to_string(),
                "iota_step".to_string(),
                "iota_step_deterministic".to_string(),
                "iota_reduct".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "list_head".to_string(),
                "list_drop".to_string(),
                "list_length".to_string(),
                "apply_spine".to_string(),
                "list_take".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "recrule_num_fields".to_string(),
                "recrule_rhs".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The arithmetic absurdity bricks the below-boundary spine congruence needs to
    /// discharge its iota_p arm. `iota_step` on a below-boundary spine forces
    /// `Le (succ major_idx) length` (the major sits past the spine), which together
    /// with the below-boundary guard `Le length major_idx` is `Le (succ K) K` — an
    /// arithmetic impossibility. Type-valued (produces `Empty`) so the spine-cong's
    /// Type-valued goal can be discharged via `Empty.rec`.
    fn add_below_boundary_bricks(&mut self) -> Result<(), SpecError> {
        // HeadConstBox o nm: a Type-valued box around the Prop equality
        // o = some nm. The below-boundary spine congruence bundles its two
        // preserved facts in AndType (Type × Type); the head-preservation fact is a
        // Prop Eq, which AndType (whose fields are Type) cannot carry directly (the
        // elaborator does not coerce Prop into Type), so it rides in this box. One
        // constructor wrapping the Prop eq ⇒ definitionally a Prop in disguise (NOT
        // an axiom; HeadConstBox.rec unwraps it).
        self.add_inductive(
            r"inductive HeadConstBox (o : OptionType Name) (nm : Name) : Type
| mk : Eq (OptionType Name) o (OptionType.some Name nm) → HeadConstBox o nm",
            "A Type-valued box around the Prop equality o = some nm, so the below-boundary \
             spine congruence can bundle the head-preservation fact alongside the (Type-valued) \
             spine congruence in AndType. One constructor wrapping the Prop eq; HeadConstBox.rec \
             unwraps. NOT an axiom. Part of #2859 (Increment F+, confluence core).",
        )?;

        // le_succ_zero_empty: Le (succ n) zero is impossible. Le : Prop is two-ctor,
        // so Le.rec is SUBSINGLETON-eliminating and CANNOT land a Type motive (-> Empty).
        // Route through Prop: Le.rec into the PROP motive Nat.sub (succ n) j = 0 (the
        // le_to_sub pattern: refl = nat_sub_self, step = pred), apply at j = 0 to get
        // hsub : Nat.sub (succ n) 0 = 0; nat_sub_zero_right gives Nat.sub (succ n) 0 =
        // succ n, so succ n = 0 (Prop Eq); the Type-valued no-confusion nat_zero_ne_succ
        // (Empty.rec bridge) refutes it into Empty.
        {
            // hsub : Eq Nat (Nat.sub (Nat.succ n) Nat.zero) Nat.zero, via Le.rec (Prop motive).
            let hsub = concat!(
                "(Le.rec (Nat.succ n) ",
                "(fun (j : Nat) (_ : Le (Nat.succ n) j) => Eq Nat (Nat.sub (Nat.succ n) j) Nat.zero) ",
                "(nat_sub_self (Nat.succ n)) ",
                "(fun (m : Nat) (_hm : Le (Nat.succ n) m) (ihm : Eq Nat (Nat.sub (Nat.succ n) m) Nat.zero) => ",
                "Eq.trans Nat (Nat.sub (Nat.succ n) (Nat.succ m)) (Nat.pred (Nat.sub (Nat.succ n) m)) Nat.zero ",
                "(Eq.refl Nat (Nat.pred (Nat.sub (Nat.succ n) m))) ",
                "(Eq.trans Nat (Nat.pred (Nat.sub (Nat.succ n) m)) (Nat.pred Nat.zero) Nat.zero ",
                "(Eq.cong Nat Nat Nat.pred (Nat.sub (Nat.succ n) m) Nat.zero ihm) (Eq.refl Nat Nat.zero))) ",
                "Nat.zero h)"
            );
            // succ n = 0: succ n = Nat.sub (succ n) 0 [symm nat_sub_zero_right] = 0 [hsub].
            let succ_eq_zero = format!(
                "(Eq.trans Nat (Nat.succ n) (Nat.sub (Nat.succ n) Nat.zero) Nat.zero \
                 (Eq.symm Nat (Nat.sub (Nat.succ n) Nat.zero) (Nat.succ n) (nat_sub_zero_right (Nat.succ n))) \
                 {hsub})"
            );
            // nat_zero_ne_succ wants Eq Nat 0 (succ n); symm of succ_eq_zero.
            let value = format!(
                "fun (n : Nat) (h : Le (Nat.succ n) Nat.zero) => \
                 nat_zero_ne_succ n Empty (Eq.symm Nat (Nat.succ n) Nat.zero {succ_eq_zero})"
            );
            self.add_definition(SpecDefinition {
                name: "le_succ_zero_empty".to_string(),
                type_src: "forall (n : Nat), Le (Nat.succ n) Nat.zero -> Empty".to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "Le (succ n) zero is impossible (Type-valued, producing Empty). Le : Prop is two-ctor so ",
                    "Le.rec cannot land a Type motive; route through Prop: Le.rec into Nat.sub (succ n) j = 0 ",
                    "(le_to_sub: refl = nat_sub_self, step = pred), applied at j = 0 gives hsub : sub (succ n) 0 ",
                    "= 0; nat_sub_zero_right gives sub (succ n) 0 = succ n, so succ n = 0; the Type-valued ",
                    "no-confusion nat_zero_ne_succ (Empty.rec bridge) refutes it. The base of le_succ_self_empty ",
                    "(the below-boundary iota_p discharge). DerivedProved, zero axiom_deps. Part of #2859 ",
                    "(Increment F+, confluence core)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "Le".to_string(),
                    "Le.rec".to_string(),
                    "Empty".to_string(),
                    "nat_sub_self".to_string(),
                    "nat_sub_zero_right".to_string(),
                    "nat_zero_ne_succ".to_string(),
                    "Nat.pred".to_string(),
                    "Nat.sub".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                    "Eq.refl".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // le_succ_self_empty: Le (succ n) n is impossible (Type-valued). Nat.rec on n:
        // n = 0 -> le_succ_zero_empty; n = succ m (IH : Le (succ m) m -> Empty) ->
        // le_pred_pred drops both succ from Le (succ (succ m)) (succ m) to Le (succ m)
        // m, then the IH. The arithmetic core of the below-boundary iota_p discharge.
        {
            let value = concat!(
                "fun (n : Nat) => ",
                "Nat.rec (fun (k : Nat) => Le (Nat.succ k) k -> Empty) ",
                // zero arm
                "(fun (h : Le (Nat.succ Nat.zero) Nat.zero) => le_succ_zero_empty Nat.zero h) ",
                // succ arm
                "(fun (m : Nat) (ihm : Le (Nat.succ m) m -> Empty) ",
                "(h : Le (Nat.succ (Nat.succ m)) (Nat.succ m)) => ",
                "ihm (le_pred_pred (Nat.succ m) m h)) ",
                "n"
            );
            self.add_definition(SpecDefinition {
                name: "le_succ_self_empty".to_string(),
                type_src: "forall (n : Nat), Le (Nat.succ n) n -> Empty".to_string(),
                value_src: Some(value.to_string()),
                is_axiom: false,
                description: concat!(
                    "Le (succ n) n is impossible (Type-valued, producing Empty): Nat.rec on n; n = 0 via ",
                    "le_succ_zero_empty; n = succ m via le_pred_pred (Le (succ (succ m)) (succ m) -> Le (succ ",
                    "m) m) onto the IH. The arithmetic core of par_reduces_p_spine_cong_below_boundary's iota_p ",
                    "discharge (a below-boundary spine cannot fire a top-level iota). DerivedProved, zero ",
                    "axiom_deps. Part of #2859 (Increment F+, confluence core)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "Le".to_string(),
                    "Nat.rec".to_string(),
                    "Empty".to_string(),
                    "le_succ_zero_empty".to_string(),
                    "le_pred_pred".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_step_below_boundary_absurd: a const-headed spine whose length is at or
        // below the recursor's major boundary cannot fire a top-level iota. Inverts
        // iota_step env e t via iota_reduct_some_inv_type to recover the head recname,
        // its meta, and h3 (the major sits at index major_idx(meta) in kapp_args e);
        // list_head_drop_some_le_succ h3 gives Le (succ major_idx(meta)) length. The
        // caller supplies head(e) = some nm, recmeta_for env nm = some meta (so the
        // recovered meta IS the guard's meta, via option_some_inj 2x), and the
        // below-boundary Le length major_idx(meta). le_trans + le_succ_self_empty close.
        {
            let major_idx = |mta: &str| -> String {
                format!(
                    "(Nat.add (Nat.add (Nat.add (recmeta_num_params {mta}) (recmeta_num_motives {mta})) (recmeta_num_minors {mta})) (recmeta_num_indices {mta}))"
                )
            };
            let mi_meta = major_idx("meta");
            let mi_meta2 = major_idx("meta2");
            let len_e = "(list_length (kapp_args e))";
            // recname2 = nm (from h1 [head e = some recname2] + hhead [head e = some nm]).
            let recname2_eq_nm = concat!(
                "(option_some_inj Name recname2 nm ",
                "(Eq.trans (OptionType Name) (OptionType.some Name recname2) ",
                "(kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) ",
                "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname2) h1) ",
                "hhead))"
            );
            // meta2 = meta: recmeta_for env recname2 = some meta2 [h2], rewrite
            // recname2 -> nm gives recmeta_for env nm = some meta2; combine with hmeta
            // (recmeta_for env nm = some meta) via option_some_inj.
            let h2_at_nm = format!(
                "(Eq.substType Name (fun (N : Name) => Eq (OptionType RecMeta) (recmeta_for env N) (OptionType.some RecMeta meta2)) recname2 nm {recname2_eq_nm} h2)"
            );
            let meta2_eq_meta = format!(
                "(option_some_inj RecMeta meta2 meta \
                 (Eq.trans (OptionType RecMeta) (OptionType.some RecMeta meta2) (recmeta_for env nm) (OptionType.some RecMeta meta) \
                 (Eq.symm (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta2) {h2_at_nm}) \
                 hmeta))"
            );
            // h3 : list_head (list_drop major_idx(meta2) (kapp_args e)) = some major.
            // le_succ : Le (succ major_idx(meta2)) length.
            let le_succ =
                format!("(list_head_drop_some_le_succ {mi_meta2} (kapp_args e) major h3)");
            // Rewrite major_idx(meta2) -> major_idx(meta) along meta2 = meta, so it
            // aligns with the below-boundary guard's major_idx(meta).
            let le_succ_at_meta = format!(
                "(Eq.substType RecMeta (fun (M : RecMeta) => Le (Nat.succ {0}) {len_e}) meta2 meta {meta2_eq_meta} {le_succ})",
                major_idx("M"),
            );
            // Le (succ major_idx(meta)) major_idx(meta) via le_trans (le_succ_at_meta,
            // hbelow : Le length major_idx(meta)), then le_succ_self_empty -> Empty ->
            // Empty.rec to C.
            let value = format!(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (t : KExpr) (nm : Name) (meta : RecMeta) (C : Type) ",
                    "(hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm)) ",
                    "(hmeta : Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta)) ",
                    "(hbelow : Le {len_e} {mi_meta}) ",
                    "(hi : iota_step env e t) => ",
                    "iota_reduct_some_inv_type env e t C hi ",
                    "(fun (recname2 : Name) (meta2 : RecMeta) (major : KExpr) (cname2 : Name) (rule2 : RecRule) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname2)) ",
                    "(h2 : Eq (OptionType RecMeta) (recmeta_for env recname2) (OptionType.some RecMeta meta2)) ",
                    "(h3 : Eq (OptionType KExpr) (list_head (list_drop {mi_meta2} (kapp_args e))) (OptionType.some KExpr major)) ",
                    "(h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname2)) ",
                    "(h5 : Eq (OptionType RecRule) (recrule_for env recname2 cname2) (OptionType.some RecRule rule2)) ",
                    "(h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ {mi_meta2}) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule2)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta2) (recmeta_num_motives meta2)) (recmeta_num_minors meta2)) (kapp_args e)) (recrule_rhs rule2))))) (OptionType.some KExpr t)) => ",
                    "Empty.rec (fun (_e : Empty) => C) ",
                    "(le_succ_self_empty {mi_meta} ",
                    "(le_trans (Nat.succ {mi_meta}) {len_e} {mi_meta} {le_succ_at_meta} hbelow)))"
                ),
                len_e = len_e,
                mi_meta = mi_meta,
                mi_meta2 = mi_meta2,
                le_succ_at_meta = le_succ_at_meta,
            );
            let type_src = format!(
                "forall (env : RecEnv) (e : KExpr) (t : KExpr) (nm : Name) (meta : RecMeta) (C : Type), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) -> \
                 Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta) -> \
                 Le {len_e} {mi_meta} -> \
                 iota_step env e t -> C",
                len_e = len_e,
                mi_meta = mi_meta,
            );
            self.add_definition(SpecDefinition {
                name: "iota_step_below_boundary_absurd".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "A const-headed spine at or below the recursor's major boundary cannot fire a top-level ",
                    "iota (Type-valued discharge). Inverts iota_step env e t via iota_reduct_some_inv_type to ",
                    "recover the recovered head/meta and h3 (the major lives at index major_idx(meta2) in ",
                    "kapp_args e); list_head_drop_some_le_succ h3 gives Le (succ major_idx(meta2)) length. The ",
                    "caller's head(e) = some nm + recmeta_for env nm = some meta identify the recovered meta2 ",
                    "with meta (option_some_inj 2x), so the Le rewrites to Le (succ major_idx(meta)) length; ",
                    "le_trans with the below-boundary guard Le length major_idx(meta) gives Le (succ K) K, ",
                    "closed by le_succ_self_empty -> Empty -> Empty.rec. DerivedProved, zero axiom_deps. Part of ",
                    "#2859 (Increment F+, confluence core)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_step".to_string(),
                    "iota_reduct_some_inv_type".to_string(),
                    "list_head_drop_some_le_succ".to_string(),
                    "le_trans".to_string(),
                    "le_succ_self_empty".to_string(),
                    "recmeta_for".to_string(),
                    "recmeta_num_params".to_string(),
                    "recmeta_num_motives".to_string(),
                    "recmeta_num_minors".to_string(),
                    "recmeta_num_indices".to_string(),
                    "kexpr_const_name".to_string(),
                    "kapp_fn".to_string(),
                    "kapp_args".to_string(),
                    "list_length".to_string(),
                    "list_head".to_string(),
                    "list_drop".to_string(),
                    "option_some_inj".to_string(),
                    "Empty".to_string(),
                    "Empty.rec".to_string(),
                    "Le".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // iota_step_no_recmeta_absurd: a const-headed spine whose head const has NO
        // recursor metadata cannot fire a top-level iota. The constructor-headed MAJOR
        // of an iota redex uses this (a constructor is not a recursor — recmeta_for
        // env cname = none, the faithful no-recmeta hypothesis). Inverts iota_step env
        // e t via iota_reduct_some_inv_type to recover h1 (head e = some recname) + h2
        // (recmeta_for env recname = some meta); head(e) = some nm gives recname = nm
        // (option_some_inj), so recmeta_for env nm = some meta, contradicting the
        // none hypothesis via option_none_ne_some_type into Empty.rec.
        {
            let recname2_eq_nm = concat!(
                "(option_some_inj Name recname2 nm ",
                "(Eq.trans (OptionType Name) (OptionType.some Name recname2) ",
                "(kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) ",
                "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname2) h1) ",
                "hhead))"
            );
            // recmeta_for env nm = some meta2 (h2 rewritten recname2 -> nm).
            let h2_at_nm = format!(
                "(Eq.substType Name (fun (N : Name) => Eq (OptionType RecMeta) (recmeta_for env N) (OptionType.some RecMeta meta2)) recname2 nm {recname2_eq_nm} h2)"
            );
            // recmeta_for env nm = none [hnone] vs = some meta2 -> Empty.
            let value = format!(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (t : KExpr) (nm : Name) (C : Type) ",
                    "(hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm)) ",
                    "(hnone : Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.none RecMeta)) ",
                    "(hi : iota_step env e t) => ",
                    "iota_reduct_some_inv_type env e t C hi ",
                    "(fun (recname2 : Name) (meta2 : RecMeta) (major : KExpr) (cname2 : Name) (rule2 : RecRule) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name recname2)) ",
                    "(h2 : Eq (OptionType RecMeta) (recmeta_for env recname2) (OptionType.some RecMeta meta2)) ",
                    "(h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta2) (recmeta_num_motives meta2)) (recmeta_num_minors meta2)) (recmeta_num_indices meta2)) (kapp_args e))) (OptionType.some KExpr major)) ",
                    "(h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname2)) ",
                    "(h5 : Eq (OptionType RecRule) (recrule_for env recname2 cname2) (OptionType.some RecRule rule2)) ",
                    "(h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta2) (recmeta_num_motives meta2)) (recmeta_num_minors meta2)) (recmeta_num_indices meta2))) (kapp_args e)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule2)) (kapp_args major)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta2) (recmeta_num_motives meta2)) (recmeta_num_minors meta2)) (kapp_args e)) (recrule_rhs rule2))))) (OptionType.some KExpr t)) => ",
                    "option_none_ne_some_type RecMeta meta2 C ",
                    "(Eq.trans (OptionType RecMeta) (OptionType.none RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta2) ",
                    "(Eq.symm (OptionType RecMeta) (recmeta_for env nm) (OptionType.none RecMeta) hnone) ",
                    "{h2_at_nm}))"
                ),
                h2_at_nm = h2_at_nm,
            );
            let type_src = concat!(
                "forall (env : RecEnv) (e : KExpr) (t : KExpr) (nm : Name) (C : Type), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) -> ",
                "Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.none RecMeta) -> ",
                "iota_step env e t -> C"
            )
            .to_string();
            self.add_definition(SpecDefinition {
                name: "iota_step_no_recmeta_absurd".to_string(),
                type_src,
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "A const-headed spine whose head const has NO recursor metadata cannot fire a top-level iota ",
                    "(Type-valued discharge). The constructor-headed MAJOR of an iota redex consumes this (a ",
                    "constructor is not a recursor: recmeta_for env cname = none, the faithful no-recmeta ",
                    "hypothesis). Inverts iota_step env e t via iota_reduct_some_inv_type to recover h1 (head e = ",
                    "some recname) + h2 (recmeta_for env recname = some meta); head(e) = some nm identifies ",
                    "recname = nm (option_some_inj), so recmeta_for env nm = some meta, contradicting the none ",
                    "hypothesis via option_none_ne_some_type into Empty.rec. DerivedProved, zero axiom_deps. Part ",
                    "of #2859 (Increment F+, confluence core)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "iota_step".to_string(),
                    "iota_reduct_some_inv_type".to_string(),
                    "recmeta_for".to_string(),
                    "kexpr_const_name".to_string(),
                    "kapp_fn".to_string(),
                    "option_some_inj".to_string(),
                    "option_none_ne_some_type".to_string(),
                    "Eq.substType".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }

    /// THE crux of this run (#2859 Increment F+, L2 wall): the boundary-guarded spine
    /// congruence `par_reduces_p_spine_cong_below_boundary`. For a const-headed app
    /// spine `f` whose spine length is at or below the recursor's iota boundary
    /// `major_idx = params+motives+minors+indices` of its head's `meta`, a
    /// `par_reduces_p` step is a SPINE congruence: `kapp_args f ⇒_p_list kapp_args f'`
    /// (and the head + spine length are preserved). The iota_p top-arm — which the
    /// unguarded c-port could not discharge (the fire is on the REDUCED premise, design
    /// §11) — is RULED OUT by the below-boundary length: a below-boundary spine cannot
    /// fire a top-level iota (`iota_step_below_boundary_absurd`).
    ///
    /// A SINGLE `par_reduces_p.rec` carrying a CPS-product motive that simultaneously
    /// delivers all three preserved facts (spine congruence, head-const preservation,
    /// length boundedness), so the iota_p arm's IH on the sub-reduction `s ⇒_p e2`
    /// supplies head(e2)=nm AND `Le (length (kapp_args e2)) major_idx` — exactly the
    /// hypotheses `iota_step_below_boundary_absurd` needs to refute the fired iota.
    fn add_par_reduces_p_spine_cong_below_boundary(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_spine_cong_below_boundary".to_string(),
            type_src: par_reduces_p_spine_cong_below_boundary_type(),
            value_src: Some(par_reduces_p_spine_cong_below_boundary_proof()),
            is_axiom: false,
            description: concat!(
                "L2 wall, CLOSED (#2859 Increment F+): the boundary-guarded spine congruence for ",
                "par_reduces_p. Under head(kapp_fn f) = some nm, recmeta_for env nm = some meta, and the ",
                "BELOW-BOUNDARY guard Le (length (kapp_args f)) major_idx(meta) (the spine is too short to have ",
                "an element at the major index, so f is a STRICT partial recursor application that can never ",
                "fire a top-level iota), a par_reduces_p step gives kapp_args f ⇒_p_list kapp_args f'. A single ",
                "par_reduces_p.rec with an AndType-PRODUCT motive bundling the two preserved facts (the spine ",
                "congruence + head-const preservation, the latter boxed in HeadConstBox so the Type-valued AndType ",
                "can carry the Prop eq) so the iota_p arm's IH supplies head(e2)=nm + the spine-cong (hence Le ",
                "(length (kapp_args e2)) major_idx via length-eq) — the hypotheses iota_step_below_boundary_absurd ",
                "needs to refute the fired iota (the redex-creation case that the c not-redex guard could NOT ",
                "discharge, design §11/§13). refl returns the products; app recurses via kapp_args_par_p on the ",
                "head IH (guard/length lifted via kapp_fn_app + list_length stability); binder/beta/let arms ",
                "discharge on the head mismatch (kapp_fn is a binder => none). DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list_refl".to_string(),
                "par_reduces_p_list_length_eq".to_string(),
                "kapp_args_par_p".to_string(),
                "iota_step_below_boundary_absurd".to_string(),
                "AndType".to_string(),
                "AndType.intro".to_string(),
                "AndType.rec".to_string(),
                "HeadConstBox".to_string(),
                "HeadConstBox.mk".to_string(),
                "HeadConstBox.rec".to_string(),
                "iota_step".to_string(),
                "iota_reduct".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "kapp_args".to_string(),
                "kapp_args_app".to_string(),
                "list_length".to_string(),
                "list_length_append_singleton".to_string(),
                "recmeta_for".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "le_trans".to_string(),
                "Le".to_string(),
                "Le.step".to_string(),
                "Le.refl".to_string(),
                "option_none_ne_some_type".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_preserves_head_const_below_boundary — the HEAD-side companion of
        // the spine congruence. Same AndType-product recursor (reused verbatim via
        // par_reduces_p_spine_cong_below_boundary_andtype), but projects + unboxes the
        // HEAD-const half of the product: under the below-boundary recursor guard, a
        // const-headed f ⇒_p f' preserves the head const (head f' = some nm). The p-side
        // analogue of the c-side par_reduces_c_preserves_head_const_nr (whose not-redex
        // guard does NOT port — design §11; the below-boundary arithmetic guard discharges
        // the iota_p arm instead). Consumed by the (iota,app) minimal-join reduct
        // reconstruction (par_reduces_p_app_redex) to lift head f = some recname to head f'.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_preserves_head_const_below_boundary".to_string(),
            type_src: par_reduces_p_preserves_head_const_below_boundary_type(),
            value_src: Some(par_reduces_p_preserves_head_const_below_boundary_proof()),
            is_axiom: false,
            description: concat!(
                "The HEAD-side companion of par_reduces_p_spine_cong_below_boundary (#2859 Increment F++): under ",
                "head(kapp_fn f) = some nm, recmeta_for env nm = some meta, and the BELOW-BOUNDARY guard ",
                "Le (length (kapp_args f)) major_idx(meta), a par_reduces_p step preserves the head const: ",
                "head(kapp_fn f') = some nm. Reuses the EXACT AndType-product recursor of the spine congruence ",
                "(identical motive + 9 arms incl. the trailing let_cong; iota_p discharged by iota_step_below_boundary_absurd) but projects + ",
                "unboxes the head-const half of the product instead of the spine half. The p-side analogue of the ",
                "c-side par_reduces_c_preserves_head_const_nr — the not-redex guard does NOT port (the p-side iota_p ",
                "fires on the reduced premise, design §11), so the below-boundary arithmetic guard discharges the ",
                "iota_p arm instead. Consumed by the (iota,app) minimal-join reduct reconstruction. DerivedProved, ",
                "zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list_refl".to_string(),
                "par_reduces_p_list_length_eq".to_string(),
                "kapp_args_par_p".to_string(),
                "iota_step_below_boundary_absurd".to_string(),
                "AndType".to_string(),
                "AndType.intro".to_string(),
                "AndType.rec".to_string(),
                "HeadConstBox".to_string(),
                "HeadConstBox.mk".to_string(),
                "HeadConstBox.rec".to_string(),
                "iota_step".to_string(),
                "iota_reduct".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "kapp_args".to_string(),
                "kapp_args_app".to_string(),
                "list_length".to_string(),
                "list_length_append_singleton".to_string(),
                "recmeta_for".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "le_trans".to_string(),
                "Le".to_string(),
                "Le.step".to_string(),
                "Le.refl".to_string(),
                "option_none_ne_some_type".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_par_reduces_p_spine_cong_no_recmeta()?;
        self.add_par_reduces_p_strict_partial_no_iota()?;

        Ok(())
    }

    /// L2 brick (#2859 Increment F+, confluence core): `par_reduces_p_strict_partial_no_iota`
    /// — a recursor application whose spine length is EXACTLY the major boundary does
    /// NOT fire a top-level iota: `iota_reduct env f = none`. This is the precise fact
    /// that the boundary inverter (`iota_reduct_app_minimal_boundary_idx`) needs from a
    /// CALLER in order to conclude `major = a` (the boundary case, not over-application)
    /// when inverting `iota_step (app f a) e1` in the kcong-sub of the kiota arm. The
    /// c-machinery threaded `iota_reduct f = none` as a faithful hypothesis; here we
    /// PROVE it from the boundary identity `length(kapp_args f) = major_idx(meta)`.
    ///
    /// Proof (CPS contradiction): `OptionType.rec` on `iota_reduct env f` with a
    /// source-equation convoy motive. The none arm returns the equation; the some arm
    /// (`iota_reduct env f = some e'`) is absurd — `iota_reduct_some_inv` recovers the
    /// recursor name `recname'`, metadata `meta'`, major `major'` and `h3' : list_head
    /// (list_drop major_idx(meta') (kapp_args f)) = some major'`. The head/meta lookups
    /// (`h1'`/`h2'`) pin `recname' = nm` (option_some_inj on hhead) and `meta' = meta`
    /// (option_some_inj on hmeta after the recname rewrite), so `major_idx(meta') =
    /// major_idx(meta) = length(kapp_args f)` (hlen). Rewriting h3' to that index gives
    /// `list_head (list_drop (length(kapp_args f)) (kapp_args f)) = some major'`, whence
    /// `list_head_drop_some_le_succ` forces `Le (succ (length(kapp_args f))) (length
    /// (kapp_args f))`, refuted by `le_succ_self_empty`. DerivedProved, zero axiom_deps.
    fn add_par_reduces_p_strict_partial_no_iota(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_strict_partial_no_iota".to_string(),
            type_src: par_reduces_p_strict_partial_no_iota_type(),
            value_src: Some(par_reduces_p_strict_partial_no_iota_proof()),
            is_axiom: false,
            description: concat!(
                "L2 brick (#2859 Increment F+): a recursor application whose spine length EQUALS the major ",
                "boundary major_idx(meta) does not fire a top-level iota — iota_reduct env f = none. The fact ",
                "the boundary inverter needs to conclude major = a (boundary, not over-application) when ",
                "inverting iota_step (app f a) e1 in the kcong-sub of the kiota arm; the c-machinery took it as ",
                "a faithful hypothesis, here it is PROVED from the boundary identity. OptionType.rec convoy on ",
                "iota_reduct env f: none arm trivial; the some arm is absurd via iota_reduct_some_inv (pin ",
                "recname'=nm, meta'=meta by option_some_inj on the head/meta lookups), then h3' rewritten by the ",
                "boundary identity gives list_head (list_drop length (kapp_args f)) = some major', whence ",
                "list_head_drop_some_le_succ forces Le (succ length) length, refuted by le_succ_self_empty. ",
                "DerivedProved, zero axiom_deps. Part of #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "iota_reduct".to_string(),
                "iota_reduct_some_inv".to_string(),
                "list_head_drop_some_le_succ".to_string(),
                "le_succ_self_empty".to_string(),
                "recmeta_num_params".to_string(),
                "recmeta_num_motives".to_string(),
                "recmeta_num_minors".to_string(),
                "recmeta_num_indices".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_args".to_string(),
                "recmeta_for".to_string(),
                "list_head".to_string(),
                "list_drop".to_string(),
                "list_length".to_string(),
                "option_some_inj".to_string(),
                "OptionType.rec".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Companion of the below-boundary spine congruence for the MAJOR premise
    /// (#2859 Increment F+): `par_reduces_p_spine_cong_no_recmeta`. The major of an
    /// iota redex is CONSTRUCTOR-headed; a constructor is not a recursor, so its head
    /// const has no recursor metadata (`recmeta_for env nm = none`, the faithful
    /// no-recmeta hypothesis). Under that guard a par_reduces_p step is a spine
    /// congruence: `kapp_args f ⇒_p_list kapp_args f'`. Same AndType-product recursion
    /// as the below-boundary variant, but the iota_p arm discharges via
    /// `iota_step_no_recmeta_absurd` (no arithmetic — head(e2)=nm + recmeta_for env nm
    /// = none contradicts the inversion's recmeta lookup), and the motive carries NO
    /// length guard.
    fn add_par_reduces_p_spine_cong_no_recmeta(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_spine_cong_no_recmeta".to_string(),
            type_src: par_reduces_p_spine_cong_no_recmeta_type(),
            value_src: Some(par_reduces_p_spine_cong_no_recmeta_proof()),
            is_axiom: false,
            description: concat!(
                "Companion of par_reduces_p_spine_cong_below_boundary for the MAJOR premise (#2859 Increment ",
                "F+): under head(kapp_fn f) = some nm and the no-recmeta guard recmeta_for env nm = none (a ",
                "constructor head has no recursor metadata — the faithful hypothesis), a par_reduces_p step is a ",
                "spine congruence kapp_args f ⇒_p_list kapp_args f'. Same AndType-product (spine-cong + boxed ",
                "head preservation) par_reduces_p.rec as the below-boundary variant, but the iota_p arm discharges ",
                "via iota_step_no_recmeta_absurd (head(e2)=nm + recmeta_for env nm = none contradicts the ",
                "inversion's recmeta lookup — no arithmetic) and the motive carries no length guard. The ",
                "constructor-headed major's spine congruence the full reduct congruence needs. DerivedProved, ",
                "zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list_refl".to_string(),
                "kapp_args_par_p".to_string(),
                "iota_step_no_recmeta_absurd".to_string(),
                "AndType".to_string(),
                "AndType.intro".to_string(),
                "AndType.rec".to_string(),
                "HeadConstBox".to_string(),
                "HeadConstBox.mk".to_string(),
                "HeadConstBox.rec".to_string(),
                "iota_step".to_string(),
                "iota_reduct".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "kapp_args".to_string(),
                "recmeta_for".to_string(),
                "option_none_ne_some_type".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // par_reduces_p_preserves_head_const_no_recmeta — the HEAD-side companion of the
        // no-recmeta spine congruence. Same AndType-product recursor (reused verbatim via
        // par_reduces_p_spine_cong_no_recmeta_andtype), but projects + unboxes the HEAD-
        // const half: under the no-recmeta constructor guard, a const-headed f ⇒_p f'
        // preserves the head const (head f' = some nm). The constructor-head companion of
        // par_reduces_p_preserves_head_const_below_boundary; consumed by the (iota,app)
        // minimal-join reduct reconstruction to lift the major's head const past g ⇒_p g'.
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_preserves_head_const_no_recmeta".to_string(),
            type_src: par_reduces_p_preserves_head_const_no_recmeta_type(),
            value_src: Some(par_reduces_p_preserves_head_const_no_recmeta_proof()),
            is_axiom: false,
            description: concat!(
                "The HEAD-side companion of par_reduces_p_spine_cong_no_recmeta (#2859 Increment F++): under ",
                "head(kapp_fn f) = some nm and the no-recmeta guard recmeta_for env nm = none, a par_reduces_p ",
                "step preserves the head const: head(kapp_fn f') = some nm. Reuses the EXACT AndType-product ",
                "recursor of the no-recmeta spine congruence (identical motive + 9 arms incl. the trailing let_cong; iota_p discharged by ",
                "iota_step_no_recmeta_absurd) but projects + unboxes the head-const half of the product instead of ",
                "the spine half. The constructor-head companion of par_reduces_p_preserves_head_const_below_boundary; ",
                "consumed by the (iota,app) minimal-join reduct reconstruction. DerivedProved, zero axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "par_reduces_p_list".to_string(),
                "par_reduces_p_list_refl".to_string(),
                "kapp_args_par_p".to_string(),
                "iota_step_no_recmeta_absurd".to_string(),
                "AndType".to_string(),
                "AndType.intro".to_string(),
                "AndType.rec".to_string(),
                "HeadConstBox".to_string(),
                "HeadConstBox.mk".to_string(),
                "HeadConstBox.rec".to_string(),
                "iota_step".to_string(),
                "iota_reduct".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "kapp_args".to_string(),
                "recmeta_for".to_string(),
                "option_none_ne_some_type".to_string(),
                "Empty".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// L2b assembly (#2859 Increment F+): the FULL reduct congruence
    /// `par_reduces_p_reduct_cong` and the complete-development triangle `cd_triangle`
    /// (L2b) + `par_strips_p` (L3). See the dedicated registration helpers.
    fn add_par_reduces_p_reduct_cong_full(&mut self) -> Result<(), SpecError> {
        self.add_par_reduces_p_app_inv()?;
        self.add_cd_iota_unfold()?;
        self.add_par_reduces_p_app_dev()?;
        self.add_par_reduces_p_beta_dev()?;
        self.add_par_reduces_p_let_dev()?;
        self.add_par_reduces_p_preserves_head_const()?;
        Ok(())
    }

    /// Step 1 of the marked-fuel `par_reduces_pL_reduct_cong` campaign (#2859
    /// Increment F++, design §16): the c→p port of the GENERIC const-head
    /// preservation `par_reduces_c_preserves_head_const` (par_reduces_c.rs:1157).
    ///
    /// Under the const-head guard `kexpr_const_name (kapp_fn e) = some nm`, a
    /// `par_reduces_p` step either preserves the const head at some intermediate
    /// term (the `ksurv` continuation) or exposes an iota fire (the `kiota`
    /// continuation). Unlike the `_nr` (not-redex-guarded) variant — whose iota_p
    /// arm must be DISCHARGED against a source-side not-redex guard that the
    /// parallel-iota relation cannot supply (the fire is on the REDUCED premise
    /// `e2`, not the source, design §11) — this generic version's iota_p arm
    /// FORWARDS the reduced-form iota fire `(e2, r, hi : iota_step env e2 r)` into
    /// the `kiota` continuation, so it ports cleanly. `par_reduces_p.rec` with the
    /// guarded-Prop motive `M s t _ := head s = some nm -> C`; refl returns
    /// `ksurv`; app lifts via `kapp_fn_app` + the head IH; the binder/beta/let arms
    /// discharge (binder head = none) via `option_none_ne_some`; the iota_p arm
    /// feeds `kiota` the fired step on `e2`.
    fn add_par_reduces_p_preserves_head_const(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_preserves_head_const".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (e' : KExpr) (nm : Name) (C : Prop), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm) -> ",
                "par_reduces_p env e e' -> ",
                "(forall (t : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name nm) -> C) -> ",
                "(forall (t1 : KExpr) (t2 : KExpr), iota_step env t1 t2 -> C) -> C"
            )
            .to_string(),
            value_src: Some(par_reduces_p_preserves_head_const_proof()),
            is_axiom: false,
            description: concat!(
                "Step 1 of the marked-fuel par_reduces_pL_reduct_cong campaign (#2859 Increment F++, design §16): ",
                "the c→p port of the GENERIC const-head preservation par_reduces_c_preserves_head_const. Under ",
                "kexpr_const_name (kapp_fn e) = some nm, a par_reduces_p step either preserves the const head at ",
                "an intermediate term (ksurv continuation) or exposes an iota fire (kiota continuation). The iota_p ",
                "arm forwards the reduced-form fire (e2, r) into kiota — it ports cleanly, unlike the _nr variant ",
                "whose iota_p arm cannot be discharged against a source-side not-redex guard (the fire is on the ",
                "reduced premise e2, not the source — design §11). par_reduces_p.rec with the guarded-Prop motive ",
                "M s t _ := head s = some nm -> C; refl returns ksurv; app lifts via kapp_fn_app + the head IH; ",
                "binder/beta/let arms discharge (binder head = none) via option_none_ne_some. DerivedProved, zero ",
                "axiom_deps."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "iota_step".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "kapp_fn_app".to_string(),
                "option_none_ne_some".to_string(),
                "Eq.subst".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The cd_triangle beta-redex (kbeta) arm, extracted as a standalone, non-circular
    /// lemma (#2859 Increment F+): `par_reduces_p_beta_dev`. When the source head is a
    /// syntactic lam `f = lam A body`, the inversion's kbeta continuation contracts the
    /// root beta to `instantiate body' arg'`, and `cd (app (lam A body) a) = instantiate
    /// (cd body)(cd a)` (cd_app_lam). Given the post-IH developments `body' ⇒_p cd body`
    /// and `arg' ⇒_p cd a`, the 1-step substitution lemma `par_subst_p` lands the
    /// contraction at the development target: `instantiate body' arg' ⇒_p instantiate
    /// (cd body)(cd a)`, transported to `cd (app (lam A body) a)` by cd_app_lam.
    /// `instantiate x y = instantiate_at x y 0` definitionally, so `par_subst_p` at
    /// `d = 0` applies directly. Uses only landed bricks; NO circularity.
    fn add_par_reduces_p_beta_dev(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_beta_dev".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (A : KExpr) (body : KExpr) (a : KExpr) (body' : KExpr) (arg' : KExpr), ",
                "par_reduces_p env body' (cd env body) -> par_reduces_p env arg' (cd env a) -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p env (instantiate body' arg') (cd env (KExpr.app (KExpr.lam A body) a))"
            )
            .to_string(),
            value_src: Some(par_reduces_p_beta_dev_proof()),
            is_axiom: false,
            description: concat!(
                "The cd_triangle beta-redex (kbeta) arm as a standalone, non-circular lemma (#2859 ",
                "Increment F+): for a lam-headed source f = lam A body, the kbeta inversion contracts the ",
                "root beta to instantiate body' arg', and cd (app (lam A body) a) = instantiate (cd body)(cd a) ",
                "(cd_app_lam). From the post-IH developments body' ⇒_p cd body and arg' ⇒_p cd a, the 1-step ",
                "substitution lemma par_subst_p (at depth 0, since instantiate x y = instantiate_at x y 0 ",
                "definitionally) lands instantiate body' arg' ⇒_p instantiate (cd body)(cd a), transported to ",
                "the development target by cd_app_lam. Threads RecEnvClosed / RecEnvLiftClosed (par_subst_p's ",
                "gates). Uses only landed bricks, NO circularity. DerivedProved, zero axiom_deps. Part of #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_subst_p".to_string(),
                "cd".to_string(),
                "cd_app_lam".to_string(),
                "instantiate".to_string(),
                "instantiate_at".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The cd_triangle LET arms (let-promotion B4) as standalone, non-circular
    /// lemmas — the zeta-vs-zeta and zeta-vs-let_cong halves of the triangle at a
    /// genuine `KExpr.let_` source (cd fires the top zeta: `cd (let_ ty val body) =
    /// instantiate (cd body)(cd val)`, cd_let):
    ///   * `par_reduces_p_let_dev` (ZETA arm — the beta_dev mechanism verbatim): the
    ///     source's zeta contraction `instantiate body' val'` reaches the development
    ///     target via the 1-step substitution lemma `par_subst_p` at depth 0, given
    ///     the post-IH developments `body' ⇒_p cd body`, `val' ⇒_p cd val`;
    ///     transported by cd_let.
    ///   * `par_reduces_p_let_cong_dev` (LET_CONG arm — congruence catches up by
    ///     FIRING the zeta the development took, the app-over-beta-redex mechanism):
    ///     `let_ ty' val' body' ⇒_p instantiate (cd body)(cd val)` in one
    ///     `par_reduces_p.let_` (zeta) step on the post-IH developments (the
    ///     type-annotation development is DROPPED — refl on ty' suffices, no
    ///     inversion needed); transported by cd_let.
    fn add_par_reduces_p_let_dev(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_let_dev".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) (val' : KExpr), ",
                "par_reduces_p env body' (cd env body) -> par_reduces_p env val' (cd env val) -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_p env (instantiate body' val') (cd env (KExpr.let_ ty val body))"
            )
            .to_string(),
            value_src: Some(par_reduces_p_let_dev_proof()),
            is_axiom: false,
            description: concat!(
                "The cd_triangle zeta (let-redex) arm as a standalone, non-circular lemma (let-promotion ",
                "B4) — the beta_dev mechanism transplanted to the genuine let_ ctor: the source's zeta ",
                "contraction instantiate body' val' reaches the development target cd (let_ ty val body) = ",
                "instantiate (cd body)(cd val) (cd_let) via the 1-step substitution lemma par_subst_p at ",
                "depth 0, from the post-IH developments body' ⇒_p cd body and val' ⇒_p cd val. Threads ",
                "RecEnvClosed / RecEnvLiftClosed (par_subst_p's gates). Uses only landed bricks, NO ",
                "circularity. DerivedProved, zero axiom_deps. Part of #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_subst_p".to_string(),
                "cd".to_string(),
                "cd_let".to_string(),
                "instantiate".to_string(),
                "instantiate_at".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "par_reduces_p_let_cong_dev".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr), ",
                "par_reduces_p env val' (cd env val) -> par_reduces_p env body' (cd env body) -> ",
                "par_reduces_p env (KExpr.let_ ty' val' body') (cd env (KExpr.let_ ty val body))"
            )
            .to_string(),
            value_src: Some(par_reduces_p_let_cong_dev_proof()),
            is_axiom: false,
            description: concat!(
                "The cd_triangle let_cong (let-congruence) arm as a standalone, non-circular lemma ",
                "(let-promotion B4) — the congruence reduct catches up by FIRING the zeta the development ",
                "took (the app-congruence-over-a-beta-redex mechanism): let_ ty' val' body' ⇒_p ",
                "instantiate (cd body)(cd val) in ONE par_reduces_p.let_ (zeta) step on the post-IH ",
                "developments val' ⇒_p cd val, body' ⇒_p cd body (the type annotation is dropped by the ",
                "zeta ctor — refl on ty' suffices, no inversion needed, exactly the guide's par_dev let_ ",
                "case); transported to cd (let_ ty val body) by cd_let. Uses only landed bricks, NO ",
                "circularity. DerivedProved, zero axiom_deps. Part of #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.let_".to_string(),
                "par_reduces_p.refl".to_string(),
                "cd".to_string(),
                "cd_let".to_string(),
                "instantiate".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// The cd_triangle app-congruence (kcong) arm, extracted as a standalone,
    /// non-circular lemma (#2859 Increment F+): `par_reduces_p_app_dev`. Given the
    /// post-IH facts `f' ⇒_p cd f`, `a' ⇒_p cd a` (the structural IHs of the triangle
    /// already discharged on `f` and `a`) plus the source steps `f ⇒_p f'`, `a ⇒_p a'`,
    /// it lands the development target: `app f' a' ⇒_p cd (app f a)`. Splits on cd's
    /// app-arm decision (`kexpr_lam_cases f`):
    ///   * `f = lam A b0` (beta present): `cd (app f a) = instantiate (cd b0)(cd a)`
    ///     (cd_app_lam). `f ⇒_p f'` ⟹ (lam_inv) `f' = lam A' b0'`; `f' ⇒_p cd f =
    ///     lam (cd A)(cd b0)` (cd_lam) ⟹ (lam_inv) `A' ⇒_p cd A`, `b0' ⇒_p cd b0`.
    ///     `par_reduces_p.beta` on those + `a' ⇒_p cd a` fires the beta.
    ///   * `kexpr_is_lam f = false`, `iota_reduct env (app (cd f)(cd a)) = some r0`:
    ///     `cd (app f a) = r0` (cd_iota_unfold). `app f' a' ⇒_p app (cd f)(cd a)`
    ///     (par_reduces_p.app on the two post-IH facts), then `par_reduces_p.iota_p`
    ///     fires the developed-spine iota.
    ///   * else (`iota_reduct … = none`): `cd (app f a) = app (cd f)(cd a)` — the plain
    ///     app congruence `par_reduces_p.app`.
    /// Uses only landed bricks; NO circularity (the iota fire is on the DEVELOPED spine
    /// `app (cd f)(cd a)`, fired in ONE iota_p step, not joined). The triangle's kcong
    /// arm; the iota_p (whole-app-reduces-then-fires) arm remains the open wall.
    fn add_par_reduces_p_app_dev(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_app_dev".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), ",
                "par_reduces_p env f f' -> par_reduces_p env a a' -> ",
                "par_reduces_p env f' (cd env f) -> par_reduces_p env a' (cd env a) -> ",
                "par_reduces_p env (KExpr.app f' a') (cd env (KExpr.app f a))"
            )
            .to_string(),
            value_src: Some(par_reduces_p_app_dev_proof()),
            is_axiom: false,
            description: concat!(
                "The cd_triangle app-congruence (kcong) arm as a standalone, non-circular lemma (#2859 ",
                "Increment F+): given f ⇒_p f', a ⇒_p a', and the post-IH developments f' ⇒_p cd f, ",
                "a' ⇒_p cd a, the reassembled app reaches the development target: app f' a' ⇒_p cd (app f a). ",
                "kexpr_lam_cases f splits the three cd app-arm branches: f a lam ⟹ cd_app_lam + ",
                "par_reduces_p.beta (component reductions A' ⇒_p cd A, b0' ⇒_p cd b0 recovered from f' ⇒_p ",
                "cd f = lam (cd A)(cd b0) via lam_inv); kexpr_is_lam f = false with a developed-spine iota ",
                "redex ⟹ cd_iota_unfold + par_reduces_p.iota_p (one iota fire on app (cd f)(cd a)); else the ",
                "plain par_reduces_p.app congruence (cd_app + opt_default none). Uses only landed bricks, NO ",
                "circularity. DerivedProved, zero axiom_deps. Part of #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.app".to_string(),
                "par_reduces_p.beta".to_string(),
                "par_reduces_p.iota_p".to_string(),
                "par_reduces_p_lam_inv".to_string(),
                "cd".to_string(),
                "cd_lam".to_string(),
                "cd_app".to_string(),
                "cd_app_lam".to_string(),
                "cd_iota_unfold".to_string(),
                "kexpr_lam_cases".to_string(),
                "kexpr_is_lam".to_string(),
                "kexpr_lam_body".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "iota_step".to_string(),
                "instantiate".to_string(),
                "lam_inj_fst".to_string(),
                "lam_inj_snd".to_string(),
                "OptionType.rec".to_string(),
                "Bool.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Target #1 (#2859 Increment F+, the cd app-arm resolution): `cd_iota_unfold`.
    /// For an application `app f a` whose ORIGINAL head `f` is not a syntactic lam
    /// (`kexpr_is_lam f = false`, so no beta redex is present) and whose DEVELOPED
    /// spine `app (cd f) (cd a)` IS an iota redex (`iota_reduct env (app (cd f)(cd a))
    /// = some r`), the complete development reduces to that reduct: `cd env (app f a) =
    /// r`. Computational unfold (the kernel reduces through cd's structural KExpr.rec
    /// app arm): `cd_app` exposes the `Bool.rec (kexpr_is_lam f)` form, `hfalse`
    /// computes it to the false branch `opt_default (iota_reduct …) (app (cd f)(cd a))`,
    /// and `hsome` computes `opt_default (some r) … = r`. All Eq.trans of three
    /// reflexivity-or-cong rewrites — no induction. The cd app-arm resolution the
    /// cd_triangle iota_p / kiota arm needs to identify the development target.
    fn add_cd_iota_unfold(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "cd_iota_unfold".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (f : KExpr) (a : KExpr) (r : KExpr), ",
                "Eq Bool (kexpr_is_lam f) Bool.false -> ",
                "Eq (OptionType KExpr) (iota_reduct env (KExpr.app (cd env f) (cd env a))) (OptionType.some KExpr r) -> ",
                "Eq KExpr (cd env (KExpr.app f a)) r"
            )
            .to_string(),
            value_src: Some(cd_iota_unfold_proof()),
            is_axiom: false,
            description: concat!(
                "Target #1 (#2859 Increment F+): the cd app-arm iota resolution. When the original head f is ",
                "not a syntactic lam (kexpr_is_lam f = false, no beta redex present) and the DEVELOPED spine ",
                "app (cd f)(cd a) is an iota redex (iota_reduct env (app (cd f)(cd a)) = some r), the complete ",
                "development is that reduct: cd env (app f a) = r. Three-step Eq.trans through cd_app (the ",
                "Bool.rec form), hfalse (computes to the false branch opt_default (iota_reduct …) (app (cd f)(cd a))), ",
                "and hsome (computes opt_default (some r) … = r) — no induction. The cd app-arm resolution the ",
                "cd_triangle iota_p / kiota arm uses to name the development target. DerivedProved, zero axiom_deps. ",
                "Part of #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "cd".to_string(),
                "cd_app".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "kexpr_is_lam".to_string(),
                "kexpr_lam_body".to_string(),
                "instantiate".to_string(),
                "Bool.rec".to_string(),
                "Eq.subst".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Target #1 (#2859 Increment F+, the enabling inversion): the CPS app
    /// shape-recovery `par_reduces_p_app_inv`. From `par_reduces_p env (app f a) t`,
    /// recover one of THREE cases via continuations (mirror of `par_reduces_c_app_inv`,
    /// par_reduces_c.rs ~1182, ported to the PARALLEL-iota relation):
    ///   * `kcong` — `t = app f' a'` with `f ⇒_p f'`, `a ⇒_p a'` (the app congruence);
    ///   * `kbeta` — `f = lam A body`, `t = instantiate body' arg'` with `A ⇒_p A'`,
    ///     `body ⇒_p body'`, `a ⇒_p arg'` (the beta redex);
    ///   * `kiota` — `t = r` with `app f a ⇒_p e2` and `iota_step env e2 r` (the
    ///     PARALLEL-iota fire: the whole `app f a` par-reduces to a redex `e2`, then
    ///     `e2` fires to `r`). The genuine-new content vs. the c-mirror: the iota_p
    ///     constructor fires on the REDUCED premise, so the continuation must carry the
    ///     intermediate `e2` and the premise `(app f a) ⇒_p e2`, NOT a bare `iota_step
    ///     env (app f a) t0`. Single `par_reduces_p.rec` with a source-equation motive;
    ///     binder arms (lam/pi/forall_) discharge via lam_ne_app / pi_ne_app
    ///     no-confusion (the source is binder-headed, never an app).
    fn add_par_reduces_p_app_inv(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_reduces_p_app_inv".to_string(),
            type_src: par_reduces_p_app_inv_type(),
            value_src: Some(par_reduces_p_app_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Target #1 (#2859 Increment F+, the enabling inversion): CPS app shape-recovery for ",
                "par_reduces_p. From par_reduces_p env (app f a) t recover one of three cases via ",
                "continuations: kcong (t = app f' a', f ⇒_p f', a ⇒_p a'), kbeta (f = lam A body, ",
                "t = instantiate body' arg', with A ⇒_p A', body ⇒_p body', a ⇒_p arg'), or kiota ",
                "(t = r with app f a ⇒_p e2 and iota_step env e2 r — the PARALLEL-iota fire on the ",
                "reduced premise). Mirror of par_reduces_c_app_inv ported to the parallel-iota relation: ",
                "the genuine-new content is the kiota continuation carrying the intermediate e2 and the ",
                "premise (app f a) ⇒_p e2 (the c-mirror's iota fires atomically on the source). Single ",
                "par_reduces_p.rec with a source-equation motive; refl folds reflexive sub-derivations; ",
                "the beta arm feeds kbeta; the app arm feeds kcong; the binder arms lam/pi/forall_ ",
                "discharge via lam_ne_app / pi_ne_app no-confusion; the let_/let_cong arms discharge via ",
                "KExpr let/app discrimination (a GENUINE let is never app-headed — under the retired ",
                "app(lam) alias the let_ arm used to feed kbeta); the iota_p ",
                "arm transports its premise to (app f a) ⇒_p e2 and feeds kiota. DerivedProved, zero ",
                "axiom_deps. Part of #2859."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_p".to_string(),
                "par_reduces_p.rec".to_string(),
                "par_reduces_p.refl".to_string(),
                "iota_step".to_string(),
                "lam_ne_app".to_string(),
                "pi_ne_app".to_string(),
                "app_inj_fst".to_string(),
                "app_inj_snd".to_string(),
                "instantiate".to_string(),
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.symm".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// cd defining-equation unfold lemmas — the Eq.refl-style rewrites the triangle /
    /// cd_refl proofs use to reduce `cd env e` to its branch on each shape (the kernel
    /// computes through the structural KExpr.rec, so these are reflexivity). The app
    /// arm stays in its `Bool.rec (kexpr_is_lam f)` form (stuck on the abstract head);
    /// `cd_app_lam` is the resolved beta branch (head is a syntactic lam).
    fn add_cd_unfold(&mut self) -> Result<(), SpecError> {
        // cd_lam / cd_pi: binder unfold cd env (HEAD ty b) = HEAD (cd ty)(cd b) — refl.
        for (name, head) in [("cd_lam", "KExpr.lam"), ("cd_pi", "KExpr.pi")] {
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src: format!(
                    "forall (env : RecEnv) (ty : KExpr) (b : KExpr), \
                     Eq KExpr (cd env ({head} ty b)) ({head} (cd env ty) (cd env b))"
                ),
                value_src: Some(format!(
                    "fun (env : RecEnv) (ty : KExpr) (b : KExpr) => \
                     Eq.refl KExpr (cd env ({head} ty b))"
                )),
                is_axiom: false,
                description: format!(
                    "cd unfold for {head}: cd env ({head} ty b) = {head} (cd env ty)(cd env b). Reflexivity \
                     (the kernel computes the KExpr.rec binder arm). Part of #2859 (Increment F+)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from(["cd".to_string(), "Eq.refl".to_string()])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // cd_let: the let/zeta arm unfold (clone of cd_app_lam's resolved-redex shape —
        // a let_ is ALWAYS a zeta redex, no gate/detector). cd env (let_ ty val body) =
        // instantiate (cd body)(cd val). Reflexivity.
        self.add_definition(SpecDefinition {
            name: "cd_let".to_string(),
            type_src: "forall (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr), \
                 Eq KExpr (cd env (KExpr.let_ ty val body)) (instantiate (cd env body) (cd env val))"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr) => \
                 Eq.refl KExpr (cd env (KExpr.let_ ty val body))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "cd unfold for the genuine let_ ctor (zeta redex always present, no gate): cd env (let_ ty val body) = instantiate (cd env body)(cd env val). Reflexivity — the beta-branch (cd_app_lam) shape transplanted to the let/zeta redex. Part of #2859 (let-promotion B4).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "cd".to_string(),
                "instantiate".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // cd_app: the raw app-arm unfold (stuck on kexpr_is_lam f for abstract f).
        self.add_definition(SpecDefinition {
            name: "cd_app".to_string(),
            type_src: "forall (env : RecEnv) (f : KExpr) (a : KExpr), \
                 Eq KExpr (cd env (KExpr.app f a)) \
                 (Bool.rec (fun (_ : Bool) => KExpr) \
                 (opt_default (iota_reduct env (KExpr.app (cd env f) (cd env a))) (KExpr.app (cd env f) (cd env a))) \
                 (instantiate (kexpr_lam_body (cd env f)) (cd env a)) \
                 (kexpr_is_lam f))"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (f : KExpr) (a : KExpr) => \
                 Eq.refl KExpr (cd env (KExpr.app f a))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "cd unfold for app (raw, stuck on kexpr_is_lam f): cd env (app f a) = Bool.rec ... (kexpr_is_lam f), with cd f / cd a the developed components. Reflexivity. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "cd".to_string(),
                "Bool.rec".to_string(),
                "opt_default".to_string(),
                "iota_reduct".to_string(),
                "instantiate".to_string(),
                "kexpr_lam_body".to_string(),
                "kexpr_is_lam".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // cd_app_lam: the resolved beta branch (head is a syntactic lam, so
        // kexpr_is_lam reduces to true and kexpr_lam_body (cd (lam A b)) = cd b).
        self.add_definition(SpecDefinition {
            name: "cd_app_lam".to_string(),
            type_src: "forall (env : RecEnv) (A : KExpr) (b : KExpr) (a : KExpr), \
                 Eq KExpr (cd env (KExpr.app (KExpr.lam A b) a)) (instantiate (cd env b) (cd env a))"
                .to_string(),
            value_src: Some(
                "fun (env : RecEnv) (A : KExpr) (b : KExpr) (a : KExpr) => \
                 Eq.refl KExpr (cd env (KExpr.app (KExpr.lam A b) a))"
                    .to_string(),
            ),
            is_axiom: false,
            description: "cd unfold for an app whose head is a syntactic lam (beta redex present): cd env (app (lam A b) a) = instantiate (cd env b)(cd env a). Reflexivity (kexpr_is_lam (lam A b) = true; kexpr_lam_body (cd (lam A b)) = cd b). The beta-branch resolution. Part of #2859 (Increment F+).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "cd".to_string(),
                "instantiate".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // kexpr_lam_cases: case-analyze whether a term is a lam. CPS dispatcher (KExpr.rec
        // on f) — either deliver A, b with f = lam A b, or the witness kexpr_is_lam f =
        // false. cd_refl's app arm uses it to split the beta branch (head a syntactic lam)
        // from the iota/app branch.
        self.add_definition(SpecDefinition {
            name: "kexpr_lam_cases".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (C : Type), ",
                "(forall (A : KExpr) (b : KExpr), Eq KExpr f (KExpr.lam A b) -> C) -> ",
                "(Eq Bool (kexpr_is_lam f) Bool.false -> C) -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (f : KExpr) (C : Type) ",
                    "(lamcont : forall (A : KExpr) (b : KExpr), Eq KExpr f (KExpr.lam A b) -> C) ",
                    "(falsecont : Eq Bool (kexpr_is_lam f) Bool.false -> C) => ",
                    "KExpr.rec ",
                    "(fun (x : KExpr) => ",
                    "(forall (A : KExpr) (b : KExpr), Eq KExpr x (KExpr.lam A b) -> C) -> ",
                    "(Eq Bool (kexpr_is_lam x) Bool.false -> C) -> C) ",
                    // sort
                    "(fun (n : Level) (_lc : forall (A : KExpr) (b : KExpr), Eq KExpr (KExpr.sort n) (KExpr.lam A b) -> C) (fc : Eq Bool (kexpr_is_lam (KExpr.sort n)) Bool.false -> C) => fc (Eq.refl Bool Bool.false)) ",
                    // bvar
                    "(fun (i : Nat) (_lc : forall (A : KExpr) (b : KExpr), Eq KExpr (KExpr.bvar i) (KExpr.lam A b) -> C) (fc : Eq Bool (kexpr_is_lam (KExpr.bvar i)) Bool.false -> C) => fc (Eq.refl Bool Bool.false)) ",
                    // app
                    "(fun (f0 : KExpr) (a0 : KExpr) (_ihf : (forall (A : KExpr) (b : KExpr), Eq KExpr f0 (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam f0) Bool.false -> C) -> C) (_iha : (forall (A : KExpr) (b : KExpr), Eq KExpr a0 (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam a0) Bool.false -> C) -> C) (_lc : forall (A : KExpr) (b : KExpr), Eq KExpr (KExpr.app f0 a0) (KExpr.lam A b) -> C) (fc : Eq Bool (kexpr_is_lam (KExpr.app f0 a0)) Bool.false -> C) => fc (Eq.refl Bool Bool.false)) ",
                    // lam
                    "(fun (ty : KExpr) (b0 : KExpr) (_ihty : (forall (A : KExpr) (b : KExpr), Eq KExpr ty (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam ty) Bool.false -> C) -> C) (_ihb : (forall (A : KExpr) (b : KExpr), Eq KExpr b0 (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam b0) Bool.false -> C) -> C) (lc : forall (A : KExpr) (b : KExpr), Eq KExpr (KExpr.lam ty b0) (KExpr.lam A b) -> C) (_fc : Eq Bool (kexpr_is_lam (KExpr.lam ty b0)) Bool.false -> C) => lc ty b0 (Eq.refl KExpr (KExpr.lam ty b0))) ",
                    // pi
                    "(fun (ty : KExpr) (b0 : KExpr) (_ihty : (forall (A : KExpr) (b : KExpr), Eq KExpr ty (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam ty) Bool.false -> C) -> C) (_ihb : (forall (A : KExpr) (b : KExpr), Eq KExpr b0 (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam b0) Bool.false -> C) -> C) (_lc : forall (A : KExpr) (b : KExpr), Eq KExpr (KExpr.pi ty b0) (KExpr.lam A b) -> C) (fc : Eq Bool (kexpr_is_lam (KExpr.pi ty b0)) Bool.false -> C) => fc (Eq.refl Bool Bool.false)) ",
                    // const
                    "(fun (nm : Name) (us : ListType Level) (_lc : forall (A : KExpr) (b : KExpr), Eq KExpr (KExpr.const nm us) (KExpr.lam A b) -> C) (fc : Eq Bool (kexpr_is_lam (KExpr.const nm us)) Bool.false -> C) => fc (Eq.refl Bool Bool.false)) ",
                    // let_ (genuine 7th ctor — never a lam)
                    "(fun (ty : KExpr) (v0 : KExpr) (b0 : KExpr) (_ihty : (forall (A : KExpr) (b : KExpr), Eq KExpr ty (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam ty) Bool.false -> C) -> C) (_ihv : (forall (A : KExpr) (b : KExpr), Eq KExpr v0 (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam v0) Bool.false -> C) -> C) (_ihb : (forall (A : KExpr) (b : KExpr), Eq KExpr b0 (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam b0) Bool.false -> C) -> C) (_lc : forall (A : KExpr) (b : KExpr), Eq KExpr (KExpr.let_ ty v0 b0) (KExpr.lam A b) -> C) (fc : Eq Bool (kexpr_is_lam (KExpr.let_ ty v0 b0)) Bool.false -> C) => fc (Eq.refl Bool Bool.false)) ",
                    // proj (never a lam)
                    "(fun (s : Name) (i : Nat) (sub : KExpr) (_ihsub : (forall (A : KExpr) (b : KExpr), Eq KExpr sub (KExpr.lam A b) -> C) -> (Eq Bool (kexpr_is_lam sub) Bool.false -> C) -> C) (_lc : forall (A : KExpr) (b : KExpr), Eq KExpr (KExpr.proj s i sub) (KExpr.lam A b) -> C) (fc : Eq Bool (kexpr_is_lam (KExpr.proj s i sub)) Bool.false -> C) => fc (Eq.refl Bool Bool.false)) ",
                    // lit (never a lam)
                    "(fun (litv : Nat) (_lc : forall (A : KExpr) (b : KExpr), Eq KExpr (KExpr.lit litv) (KExpr.lam A b) -> C) (fc : Eq Bool (kexpr_is_lam (KExpr.lit litv)) Bool.false -> C) => fc (Eq.refl Bool Bool.false)) ",
                    "f lamcont falsecont"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Case-analyze whether a term is a lam (CPS, KExpr.rec on f): deliver A, b with f = lam A b (lam arm), or the witness kexpr_is_lam f = false (every other arm, by reflexivity). cd_refl's app arm splits the beta branch from the iota/app branch with it. DerivedProved, zero axiom_deps. Part of #2859 (Increment F+, complete development).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "kexpr_is_lam".to_string(),
                "KExpr.rec".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

/// Closed proof term for `cd_iota_unfold`. Three `Eq.trans`-chained rewrites:
///   (1) `cd_app env f a` : `cd (app f a) = Bool.rec _ false-arm true-arm (kexpr_is_lam f)`;
///   (2) `hfalse : kexpr_is_lam f = false` rewrites the discriminee, so the Bool.rec
///       computes (refl) to the false arm `opt_default (iota_reduct env (app cdf cda))
///       (app cdf cda)`;
///   (3) `hsome : iota_reduct env (app cdf cda) = some r` rewrites the OptionType, so
///       `opt_default (some r) dflt` computes (refl) to `r`.
/// `cdf = cd env f`, `cda = cd env a`, `dflt = app cdf cda`, `opt = iota_reduct env
/// (app cdf cda)`. Step (2) is an `Eq.subst` on the Bool discriminee (the Bool.rec
/// false-arm value is exactly `opt_default opt dflt`); step (3) is an `Eq.cong` of
/// `(fun o => opt_default o dflt)` over `hsome`, then `opt_default (some r) dflt = r`
/// by refl.
fn cd_iota_unfold_proof() -> String {
    let cdf = "(cd env f)";
    let cda = "(cd env a)";
    let dflt = "(KExpr.app (cd env f) (cd env a))";
    let opt = "(iota_reduct env (KExpr.app (cd env f) (cd env a)))";

    // (1)+(2): cd (app f a) = opt_default opt dflt. Same `eq_cd` shape as cd_refl's
    // false branch: cd_app gives the Bool.rec form; Eq.subst rewrites
    // (kexpr_is_lam f) -> Bool.false (hfalse), computing the Bool.rec to its false arm
    // value opt_default opt dflt.
    let eq_cd = format!(
        concat!(
            "(Eq.subst Bool ",
            "(fun (bcond : Bool) => Eq KExpr (cd env (KExpr.app f a)) ",
            "(Bool.rec (fun (_ : Bool) => KExpr) ",
            "(opt_default {opt} {dflt}) ",
            "(instantiate (kexpr_lam_body {cdf}) {cda}) bcond)) ",
            "(kexpr_is_lam f) Bool.false hfalse ",
            "(cd_app env f a))"
        ),
        opt = opt,
        dflt = dflt,
        cdf = cdf,
        cda = cda,
    );

    // (3a): opt_default opt dflt = opt_default (some r) dflt, by Eq.cong over hsome.
    let eq_optsome = format!(
        concat!(
            "(Eq.cong (OptionType KExpr) KExpr ",
            "(fun (o : OptionType KExpr) => opt_default o {dflt}) ",
            "{opt} (OptionType.some KExpr r) hsome)"
        ),
        opt = opt,
        dflt = dflt,
    );

    // (3b): opt_default (some r) dflt = r, by reflexivity (OptionType.rec some arm).
    let eq_r = format!(
        "(Eq.refl KExpr (opt_default (OptionType.some KExpr r) {dflt}))",
        dflt = dflt,
    );

    // Chain: cd (app f a) = opt_default opt dflt = opt_default (some r) dflt = r.
    format!(
        concat!(
            "fun (env : RecEnv) (f : KExpr) (a : KExpr) (r : KExpr) ",
            "(hfalse : Eq Bool (kexpr_is_lam f) Bool.false) ",
            "(hsome : Eq (OptionType KExpr) {opt} (OptionType.some KExpr r)) => ",
            "Eq.trans KExpr (cd env (KExpr.app f a)) (opt_default {opt} {dflt}) r ",
            "{eq_cd} ",
            "(Eq.trans KExpr (opt_default {opt} {dflt}) (opt_default (OptionType.some KExpr r) {dflt}) r ",
            "{eq_optsome} {eq_r}))"
        ),
        opt = opt,
        dflt = dflt,
        eq_cd = eq_cd,
        eq_optsome = eq_optsome,
        eq_r = eq_r,
    )
}

/// Closed proof term for `par_reduces_p_app_dev` — the cd_triangle kcong arm. Splits
/// `kexpr_lam_cases f` into the beta branch (f a syntactic lam) and the false branch
/// (kexpr_is_lam f = false → an OptionType convoy on the developed-spine iota_reduct).
/// The structure mirrors cd_refl's app arm, but with the post-IH developments
/// `hf' : f' ⇒_p cd f`, `ha' : a' ⇒_p cd a` supplied as hypotheses (cd_refl recovered
/// them from its own KExpr.rec IHs on f / a) and the source steps `hf : f ⇒_p f'`,
/// `ha : a ⇒_p a'` carried for the lam-branch lam_inv.
fn par_reduces_p_app_dev_proof() -> String {
    let cdf = "(cd env f)";
    let cda = "(cd env a)";
    let dflt = "(KExpr.app (cd env f) (cd env a))";
    let opt = "(iota_reduct env (KExpr.app (cd env f) (cd env a)))";

    // The reassembled-app congruence app f' a' ⇒_p app (cd f)(cd a), from the two
    // post-IH developments hf', ha'.
    let app_cong = "(par_reduces_p.app env f' (cd env f) a' (cd env a) hf' ha')";

    // ===== FALSE branch (kexpr_is_lam f = false): OptionType convoy on opt. =====
    // none arm: opt_default none dflt = dflt = app cdf cda → app congruence.
    let conv_none = format!(
        "(fun (eqn : Eq (OptionType KExpr) {opt} (OptionType.none KExpr)) => {app_cong})",
        opt = opt,
        app_cong = app_cong,
    );
    // some arm: opt = some r0 is iota_step env dflt r0; iota_p fires the developed spine.
    let conv_some = format!(
        concat!(
            "(fun (r0 : KExpr) (eqn : Eq (OptionType KExpr) {opt} (OptionType.some KExpr r0)) => ",
            "par_reduces_p.iota_p env (KExpr.app f' a') {dflt} r0 {app_cong} eqn)"
        ),
        opt = opt,
        dflt = dflt,
        app_cong = app_cong,
    );
    // convoy motive over o : OptionType KExpr.
    let conv_motive = format!(
        concat!(
            "(fun (o : OptionType KExpr) => Eq (OptionType KExpr) {opt} o -> ",
            "par_reduces_p env (KExpr.app f' a') (opt_default o {dflt}))"
        ),
        opt = opt,
        dflt = dflt,
    );
    // proof of app f' a' ⇒_p opt_default opt dflt.
    let on_opt_default = format!(
        concat!(
            "(OptionType.rec KExpr {conv_motive} {conv_none} {conv_some} {opt} ",
            "(Eq.refl (OptionType KExpr) {opt}))"
        ),
        conv_motive = conv_motive,
        conv_none = conv_none,
        conv_some = conv_some,
        opt = opt,
    );
    // eq_cd : cd (app f a) = opt_default opt dflt (cd_app + hfalse).
    let eq_cd = format!(
        concat!(
            "(Eq.subst Bool ",
            "(fun (bcond : Bool) => Eq KExpr (cd env (KExpr.app f a)) ",
            "(Bool.rec (fun (_ : Bool) => KExpr) ",
            "(opt_default {opt} {dflt}) ",
            "(instantiate (kexpr_lam_body {cdf}) {cda}) bcond)) ",
            "(kexpr_is_lam f) Bool.false hfalse ",
            "(cd_app env f a))"
        ),
        opt = opt,
        dflt = dflt,
        cdf = cdf,
        cda = cda,
    );
    let false_branch = format!(
        concat!(
            "(fun (hfalse : Eq Bool (kexpr_is_lam f) Bool.false) => ",
            "Eq.substType KExpr ",
            "(fun (x : KExpr) => par_reduces_p env (KExpr.app f' a') x) ",
            "(opt_default {opt} {dflt}) (cd env (KExpr.app f a)) ",
            "(Eq.symm KExpr (cd env (KExpr.app f a)) (opt_default {opt} {dflt}) {eq_cd}) ",
            "{on_opt_default})"
        ),
        opt = opt,
        dflt = dflt,
        eq_cd = eq_cd,
        on_opt_default = on_opt_default,
    );

    // ===== LAM branch (f = lam A b0). =====
    // hf transported to (lam A b0) ⇒_p f'.  hf' : f' ⇒_p cd f; rewrite cd f to
    // lam (cd A)(cd b0) (cd_lam), so f' ⇒_p lam (cd A)(cd b0).
    let hf_lam = "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x f') f (KExpr.lam A b0) hflam hf)";
    let hf_dev_lam = concat!(
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env f' x) ",
        "(cd env f) (KExpr.lam (cd env A) (cd env b0)) ",
        "(Eq.substType KExpr (fun (g : KExpr) => Eq KExpr (cd env g) (KExpr.lam (cd env A) (cd env b0))) ",
        "(KExpr.lam A b0) f (Eq.symm KExpr f (KExpr.lam A b0) hflam) (cd_lam env A b0)) ",
        "hf')"
    );
    // Goal at the lam branch: app f' a' ⇒_p instantiate (cd b0)(cd a) (= cd (app (lam A b0) a)).
    let _beta_goal_lam =
        "(par_reduces_p env (KExpr.app f' a') (instantiate (cd env b0) (cd env a)))";
    // First lam_inv: from (lam A b0) ⇒_p f' recover f' = lam A' b0', A ⇒_p A', b0 ⇒_p b0'.
    // Then SECOND lam_inv on (lam A' b0') ⇒_p lam (cd A)(cd b0) (= hf_dev_lam transported)
    // recovers A' ⇒_p cd A, b0' ⇒_p cd b0. Build par_reduces_p.beta + rewrite f' = lam A' b0'.
    //
    // klam1 A' b0' (hA : A ⇒_p A') (hb0 : b0 ⇒_p b0') (zeq1 : lam A' b0' = lam A' b0' [the inv's
    // delivered shape]) : we need C (lam A' b0') where C g := Eq g (lam A' b0') -> beta_goal at f'=g.
    // We instead pass C g := par_reduces_p env (KExpr.app g a') (instantiate (cd b0)(cd a)) and
    // use lam_inv with the equation convoy.
    //
    // Inner builder: given f' = lam A' b0', A' ⇒_p cd A, b0' ⇒_p cd b0, fire beta.
    let beta_fire =
        "(par_reduces_p.beta env A' (cd env A) b0' (cd env b0) a' (cd env a) hA'cdA hb0'cdb0 ha')";
    // klam2: second lam_inv continuation. ty2 body2 (hty2 : A' ⇒_p ty2)(hbody2 : b0' ⇒_p body2)
    // zeq2 : lam ty2 body2 = lam (cd A)(cd b0). Rewrite ty2 → cd A, body2 → cd b0.
    let klam2 = format!(
        concat!(
            "(fun (ty2 : KExpr) (body2 : KExpr) ",
            "(hty2 : par_reduces_p env A' ty2) (hbody2 : par_reduces_p env b0' body2) ",
            "(zeq2 : Eq KExpr (KExpr.lam ty2 body2) (KExpr.lam (cd env A) (cd env b0))) => ",
            "(fun (hA'cdA : par_reduces_p env A' (cd env A)) (hb0'cdb0 : par_reduces_p env b0' (cd env b0)) => ",
            "{beta_fire}) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env A' x) ty2 (cd env A) ",
            "(lam_inj_fst ty2 body2 (cd env A) (cd env b0) zeq2) hty2) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env b0' x) body2 (cd env b0) ",
            "(lam_inj_snd ty2 body2 (cd env A) (cd env b0) zeq2) hbody2))"
        ),
        beta_fire = beta_fire,
    );
    // klam1: first lam_inv continuation. A' b0' (hA : A ⇒_p A')(hb0 : b0 ⇒_p b0')
    // zeq1 : lam A' b0' = lam A' b0' (the convoy's self-eq, used to rewrite f' → lam A' b0').
    // Build beta_goal at f' = lam A' b0' by feeding the SECOND lam_inv on hf_dev_lam-at-(lam A' b0').
    // We run lam_inv on hf_dev_lam (f' ⇒_p lam (cd A)(cd b0)) but with f' already = lam A' b0', so
    // transport hf_dev_lam to (lam A' b0') ⇒_p lam (cd A)(cd b0) first.
    let klam1 = format!(
        concat!(
            "(fun (A' : KExpr) (b0' : KExpr) ",
            "(hA : par_reduces_p env A A') (hb0 : par_reduces_p env b0 b0') ",
            "(zeq1 : Eq KExpr (KExpr.lam A' b0') f') => ",
            "Eq.substType KExpr (fun (g : KExpr) => par_reduces_p env (KExpr.app g a') (instantiate (cd env b0) (cd env a))) ",
            "(KExpr.lam A' b0') f' zeq1 ",
            "(par_reduces_p_lam_inv env A' b0' (KExpr.lam (cd env A) (cd env b0)) ",
            "(fun (z : KExpr) => Eq KExpr z (KExpr.lam (cd env A) (cd env b0)) -> par_reduces_p env (KExpr.app (KExpr.lam A' b0') a') (instantiate (cd env b0) (cd env a))) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x (KExpr.lam (cd env A) (cd env b0))) ",
            "f' (KExpr.lam A' b0') (Eq.symm KExpr (KExpr.lam A' b0') f' zeq1) {hf_lam_dev}) ",
            "{klam2_inner} ",
            "(Eq.refl KExpr (KExpr.lam (cd env A) (cd env b0)))))"
        ),
        hf_lam_dev = hf_dev_lam,
        klam2_inner = klam2,
    );
    // p_lam : the lam-branch proof, transported from instantiate (cd b0)(cd a) to
    // cd (app (lam A b0) a) via cd_app_lam.
    let p_lam = format!(
        concat!(
            "(Eq.substType KExpr ",
            "(fun (x : KExpr) => par_reduces_p env (KExpr.app f' a') x) ",
            "(instantiate (cd env b0) (cd env a)) (cd env (KExpr.app (KExpr.lam A b0) a)) ",
            "(Eq.symm KExpr (cd env (KExpr.app (KExpr.lam A b0) a)) (instantiate (cd env b0) (cd env a)) ",
            "(cd_app_lam env A b0 a)) ",
            "(par_reduces_p_lam_inv env A b0 f' ",
            "(fun (z : KExpr) => Eq KExpr z f' -> {beta_goal_lam_at_app}) ",
            "{hf_lam} {klam1} (Eq.refl KExpr f')))"
        ),
        beta_goal_lam_at_app =
            "(par_reduces_p env (KExpr.app f' a') (instantiate (cd env b0) (cd env a)))",
        hf_lam = hf_lam,
        klam1 = klam1,
    );
    // lam_branch: rewrite the goal's cd (app f a) by f = lam A b0 (hflam) so cd_app_lam
    // applies, prove P at f = lam A b0, then transport back to f.
    let lam_branch = format!(
        concat!(
            "(fun (A : KExpr) (b0 : KExpr) (hflam : Eq KExpr f (KExpr.lam A b0)) => ",
            "Eq.substType KExpr ",
            "(fun (g : KExpr) => par_reduces_p env (KExpr.app f' a') (cd env (KExpr.app g a))) ",
            "(KExpr.lam A b0) f ",
            "(Eq.symm KExpr f (KExpr.lam A b0) hflam) ",
            "{p_lam})"
        ),
        p_lam = p_lam,
    );

    format!(
        concat!(
            "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
            "(hf : par_reduces_p env f f') (ha : par_reduces_p env a a') ",
            "(hf' : par_reduces_p env f' (cd env f)) (ha' : par_reduces_p env a' (cd env a)) => ",
            "kexpr_lam_cases f (par_reduces_p env (KExpr.app f' a') (cd env (KExpr.app f a))) ",
            "{lam_branch} {false_branch}"
        ),
        lam_branch = lam_branch,
        false_branch = false_branch,
    )
}

/// Closed proof term for `par_reduces_p_beta_dev` — the cd_triangle kbeta arm.
/// `par_subst_p env body' (cd body) arg' (cd a) Nat.zero (body' ⇒_p cd body)
/// (arg' ⇒_p cd a) closed liftclosed` yields `par_reduces_p env (instantiate_at body'
/// arg' 0)(instantiate_at (cd body)(cd a) 0)`, which is `instantiate body' arg' ⇒_p
/// instantiate (cd body)(cd a)` (instantiate x y = instantiate_at x y 0 definitionally).
/// Transport the RHS `instantiate (cd body)(cd a) → cd (app (lam A body) a)` via
/// `Eq.symm (cd_app_lam env A body a)`.
fn par_reduces_p_beta_dev_proof() -> String {
    // The substitution step at depth 0 (definitionally instantiate body' arg' ⇒_p
    // instantiate (cd body)(cd a)).
    let subst_step = concat!(
        "(par_subst_p env body' (cd env body) arg' (cd env a) Nat.zero ",
        "hbody harg closed liftclosed)"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (A : KExpr) (body : KExpr) (a : KExpr) (body' : KExpr) (arg' : KExpr) ",
            "(hbody : par_reduces_p env body' (cd env body)) (harg : par_reduces_p env arg' (cd env a)) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "Eq.substType KExpr ",
            "(fun (x : KExpr) => par_reduces_p env (instantiate body' arg') x) ",
            "(instantiate (cd env body) (cd env a)) (cd env (KExpr.app (KExpr.lam A body) a)) ",
            "(Eq.symm KExpr (cd env (KExpr.app (KExpr.lam A body) a)) (instantiate (cd env body) (cd env a)) ",
            "(cd_app_lam env A body a)) ",
            "{subst_step}"
        ),
        subst_step = subst_step,
    )
}

/// Closed proof term for `par_reduces_p_let_dev` — `par_reduces_p_beta_dev_proof`
/// transplanted to the genuine let_ ctor (cd_app_lam → cd_let; arg → val). The
/// substitution step is `par_subst_p` at depth 0 on the two post-IH developments.
fn par_reduces_p_let_dev_proof() -> String {
    // The substitution step at depth 0 (definitionally instantiate body' val' ⇒_p
    // instantiate (cd body)(cd val)).
    let subst_step = concat!(
        "(par_subst_p env body' (cd env body) val' (cd env val) Nat.zero ",
        "hbody hval closed liftclosed)"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (val : KExpr) (body : KExpr) (body' : KExpr) (val' : KExpr) ",
            "(hbody : par_reduces_p env body' (cd env body)) (hval : par_reduces_p env val' (cd env val)) ",
            "(closed : RecEnvClosed env) (liftclosed : RecEnvLiftClosed env) => ",
            "Eq.substType KExpr ",
            "(fun (x : KExpr) => par_reduces_p env (instantiate body' val') x) ",
            "(instantiate (cd env body) (cd env val)) (cd env (KExpr.let_ ty val body)) ",
            "(Eq.symm KExpr (cd env (KExpr.let_ ty val body)) (instantiate (cd env body) (cd env val)) ",
            "(cd_let env ty val body)) ",
            "{subst_step}"
        ),
        subst_step = subst_step,
    )
}

/// Closed proof term for `par_reduces_p_let_cong_dev` — the congruence reduct fires
/// the zeta the development took: ONE `par_reduces_p.let_` step (ty-annotation
/// development dropped, refl on ty'), transported by `cd_let`.
fn par_reduces_p_let_cong_dev_proof() -> String {
    // The zeta fire: let_ ty' val' body' ⇒_p instantiate (cd body)(cd val).
    let zeta_step = concat!(
        "(par_reduces_p.let_ env ty' ty' val' (cd env val) body' (cd env body) ",
        "(par_reduces_p.refl env ty') hval hbody)"
    );
    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) ",
            "(body : KExpr) (body' : KExpr) ",
            "(hval : par_reduces_p env val' (cd env val)) (hbody : par_reduces_p env body' (cd env body)) => ",
            "Eq.substType KExpr ",
            "(fun (x : KExpr) => par_reduces_p env (KExpr.let_ ty' val' body') x) ",
            "(instantiate (cd env body) (cd env val)) (cd env (KExpr.let_ ty val body)) ",
            "(Eq.symm KExpr (cd env (KExpr.let_ ty val body)) (instantiate (cd env body) (cd env val)) ",
            "(cd_let env ty val body)) ",
            "{zeta_step}"
        ),
        zeta_step = zeta_step,
    )
}

/// Closed proof term for `par_reduces_p_lam_reduct_not_redex` (L1a prerequisite).
/// Type-valued (so `par_reduces_p.rec`'s motive lands in Type): from a lam-headed
/// par-step `(lam ty body) ⇒_p t` and a fired iota `iota_step env t r`, derive any
/// `C : Type`. The motive universalizes the new redex `(r2, C2)` and threads
/// `iota_step env e' r2 → C2`. refl/lam reducts are binder-headed (lam), so the iota
/// on them is absurd (`iota_step_head_none_absurd_type` on the none head, computed by
/// refl); beta/app are app-headed (`app_ne_lam`), pi/forall_ pi-headed
/// (`pi_ne_lam`), let_/let_cong let-headed (the CD_KEXPR_NOT_LAM discriminator — a
/// genuine let is never a lam); the iota_p arm discharges via its OWN IH applied to the
/// constructor's FIRE premise (the reduced sub-redex is again a par-reduct of the lam,
/// hence not a redex), so the new outer iota is irrelevant.
fn par_reduces_p_lam_reduct_not_redex_proof() -> String {
    // Motive over (e ⇒_p e'): from e = lam ty body, the reduct e' is not a redex for
    // ANY new redex r2 — concluding Empty (Sort 1 = Type, so the recursor motive lands
    // in Type WITHOUT quantifying over an arbitrary Type C2, which would push the
    // motive to Sort 2 and the recursor rejects it). The outer wrapper turns Empty
    // into any C via Empty.rec.
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p env e e') => ",
        "Eq KExpr e (KExpr.lam ty body) -> ",
        "forall (r2 : KExpr), iota_step env e' r2 -> Empty)"
    );
    // The IH shape for a sub-derivation SUB ⇒ SUB'.
    let ih = concat!(
        "Eq KExpr SUB (KExpr.lam ty body) -> ",
        "forall (r2 : KExpr), iota_step env SUB' r2 -> Empty"
    );

    // Discharge a binder-headed (lam) reduct LAMRED: iota_step env LAMRED r2 (named
    // HIN) is absurd (kexpr_const_name (kapp_fn LAMRED) = none, by refl on a lam head).
    // Empty as the Type-valued discharge target.
    let lam_head_discharge = |lamred: &str, hin: &str| -> String {
        format!(
            concat!(
                "(iota_step_head_none_absurd_type env {lamred} r2 Empty ",
                "(Eq.refl (OptionType Name) (kexpr_const_name (kapp_fn {lamred}))) {hin})"
            ),
            lamred = lamred,
            hin = hin,
        )
    };

    // refl: reduct e; rewrite e -> lam ty body, the reduct is the lam (binder-headed).
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.lam ty body)) ",
            "(r2 : KExpr) (hi2 : iota_step env e r2) => ",
            "Eq.substType KExpr ",
            "(fun (x : KExpr) => iota_step env x r2 -> Empty) ",
            "(KExpr.lam ty body) e ",
            "(Eq.symm KExpr e (KExpr.lam ty body) eq) ",
            "(fun (hi3 : iota_step env (KExpr.lam ty body) r2) => {discharge}) ",
            "hi2)"
        ),
        discharge = lam_head_discharge("(KExpr.lam ty body)", "hi3"),
    );

    // beta: source app (lam A b0) arg — app /= lam.
    let beta_arm = format!(
        concat!(
            "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(_hA : par_reduces_p env A A') (_hb0 : par_reduces_p env b0 b0') ",
            "(_harg : par_reduces_p env arg arg') ",
            "(_ihA : {ih_A}) (_ihb0 : {ih_b0}) (_iharg : {ih_arg}) ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.lam ty body)) => ",
            "app_ne_lam (KExpr.lam A b0) arg ty body ",
            "(forall (r2 : KExpr), iota_step env (instantiate b0' arg') r2 -> Empty) eq)"
        ),
        ih_A = ih.replace("SUB'", "A'").replace("SUB", "A"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
        ih_arg = ih.replace("SUB'", "arg'").replace("SUB", "arg"),
    );

    // app: source app g b — app /= lam.
    let app_arm = format!(
        concat!(
            "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(_hg : par_reduces_p env g g') (_hb : par_reduces_p env b b') ",
            "(_ihg : {ih_g}) (_ihb : {ih_b}) ",
            "(eq : Eq KExpr (KExpr.app g b) (KExpr.lam ty body)) => ",
            "app_ne_lam g b ty body ",
            "(forall (r2 : KExpr), iota_step env (KExpr.app g' b') r2 -> Empty) eq)"
        ),
        ih_g = ih.replace("SUB'", "g'").replace("SUB", "g"),
        ih_b = ih.replace("SUB'", "b'").replace("SUB", "b"),
    );

    // lam: source lam t0 b0 — reduct lam t0' b0' (binder-headed), iota absurd.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht : par_reduces_p env t0 t0') (_hb : par_reduces_p env b0 b0') ",
            "(_iht : {ih_t0}) (_ihb : {ih_b0}) ",
            "(_eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.lam ty body)) ",
            "(r2 : KExpr) (hi2 : iota_step env (KExpr.lam t0' b0') r2) => {discharge})"
        ),
        ih_t0 = ih.replace("SUB'", "t0'").replace("SUB", "t0"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
        discharge = lam_head_discharge("(KExpr.lam t0' b0')", "hi2"),
    );

    // pi: source pi dom b0 — pi /= lam.
    let pi_arm = format!(
        concat!(
            "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_p env dom dom') (_hb0 : par_reduces_p env b0 b0') ",
            "(_ihd : {ih_dom}) (_ihb0 : {ih_b0}) ",
            "(eq : Eq KExpr (KExpr.pi dom b0) (KExpr.lam ty body)) => ",
            "pi_ne_lam dom b0 ty body ",
            "(forall (r2 : KExpr), iota_step env (KExpr.pi dom' b0') r2 -> Empty) eq)"
        ),
        ih_dom = ih.replace("SUB'", "dom'").replace("SUB", "dom"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
    );

    // forall_: source forall_ dom b0 = pi dom b0 (alias) — pi /= lam.
    let forall_arm = format!(
        concat!(
            "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_p env dom dom') (_hb0 : par_reduces_p env b0 b0') ",
            "(_ihd : {ih_dom}) (_ihb0 : {ih_b0}) ",
            "(eq : Eq KExpr (KExpr.forall_ dom b0) (KExpr.lam ty body)) => ",
            "pi_ne_lam dom b0 ty body ",
            "(forall (r2 : KExpr), iota_step env (KExpr.forall_ dom' b0') r2 -> Empty) eq)"
        ),
        ih_dom = ih.replace("SUB'", "dom'").replace("SUB", "dom"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
    );

    // let_ (ZETA): source let_ t0 v b0 (a genuine let, NEVER a lam) — refute the
    // source equation via the let/lam discriminator (app_ne_lam covered it only
    // under the retired app(lam) alias).
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : {ih_t0}) (_ihv : {ih_v}) (_ihb0 : {ih_b0}) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
            "Empty.rec (fun (_ : Empty) => ",
            "forall (r2 : KExpr), iota_step env (instantiate b0' v') r2 -> Empty) ",
            "(Eq.substType KExpr {discr} (KExpr.let_ t0 v b0) (KExpr.lam ty body) eq Nat.zero))"
        ),
        ih_t0 = ih.replace("SUB'", "t0'").replace("SUB", "t0"),
        ih_v = ih.replace("SUB'", "v'").replace("SUB", "v"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
        discr = CD_KEXPR_NOT_LAM,
    );

    // let_cong (trailing CONGRUENCE): source let_ t0 v b0 (never a lam) — same
    // refutation, reduct KExpr.let_ t0' v' b0'.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : {ih_t0}) (_ihv : {ih_v}) (_ihb0 : {ih_b0}) ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
            "Empty.rec (fun (_ : Empty) => ",
            "forall (r2 : KExpr), iota_step env (KExpr.let_ t0' v' b0') r2 -> Empty) ",
            "(Eq.substType KExpr {discr} (KExpr.let_ t0 v b0) (KExpr.lam ty body) eq Nat.zero))"
        ),
        ih_t0 = ih.replace("SUB'", "t0'").replace("SUB", "t0"),
        ih_v = ih.replace("SUB'", "v'").replace("SUB", "v"),
        ih_b0 = ih.replace("SUB'", "b0'").replace("SUB", "b0"),
        discr = CD_KEXPR_NOT_LAM,
    );

    // iota_p: source e0 ⇒_p e2 (the FIRE on e2: iota_step env e2 r0; reduct r0).
    // From eq : e0 = lam ty body, the IH says e2 (a par-reduct of the lam) is not a
    // redex; apply it to the FIRE premise (r0, hi0) for Empty — the new outer iota
    // (hi2 : iota_step env r0 r2) is unused.
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e2 : KExpr) (r0 : KExpr) ",
            "(_hprem : par_reduces_p env e0 e2) (hi0 : iota_step env e2 r0) ",
            "(ihprem : {ih_e0e2}) ",
            "(eq : Eq KExpr e0 (KExpr.lam ty body)) ",
            "(r2 : KExpr) (_hi2 : iota_step env r0 r2) => ",
            "ihprem eq r0 hi0)"
        ),
        ih_e0e2 = ih.replace("SUB'", "e2").replace("SUB", "e0"),
    );

    // proj arm: source proj s i sub (never lam-headed) — refute via CD_KEXPR_NOT_LAM.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p env sub sub') ",
            "(_ihsub : {ih_sub}) ",
            "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam ty body)) => ",
            "Empty.rec (fun (_ : Empty) => ",
            "forall (r2 : KExpr), iota_step env (KExpr.proj s i sub') r2 -> Empty) ",
            "(Eq.substType KExpr {discr} (KExpr.proj s i sub) (KExpr.lam ty body) eq Nat.zero))"
        ),
        ih_sub = ih.replace("SUB'", "sub'").replace("SUB", "sub"),
        discr = CD_KEXPR_NOT_LAM,
    );

    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (r : KExpr) (C : Type) ",
            "(h : par_reduces_p env (KExpr.lam ty body) t) (hi : iota_step env t r) => ",
            "Empty.rec (fun (_e : Empty) => C) ",
            "(par_reduces_p.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.lam ty body) t h (Eq.refl KExpr (KExpr.lam ty body)) r hi)"
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
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `par_reduces_p_lam_inv` (L1a). Mirrors
/// `par_reduces_c_lam_inv_proof` over `par_reduces_p` (env threaded), with the
/// genuine-new PARALLEL-iota arm: the iota fires on the REDUCED redex `e2` (premise
/// `e0 ⇒_p e2`), so it is discharged by transporting the premise to
/// `(lam ty body) ⇒_p e2`, learning `e2` is head-none via `par_reduces_p_lam_head_none`,
/// then `iota_step_head_none_absurd_type` on the fired iota at `e2`.
fn par_reduces_p_lam_inv_proof() -> String {
    let motive = concat!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p env e e') => ",
        "Eq KExpr e (KExpr.lam ty body) -> C e')"
    );

    // refl: reduct e; build C (lam ty body), transport to C e.
    let refl_arm = concat!(
        "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.lam ty body)) => ",
        "Eq.substType KExpr C (KExpr.lam ty body) e ",
        "(Eq.symm KExpr e (KExpr.lam ty body) eq) ",
        "(klam ty body (par_reduces_p.refl env ty) (par_reduces_p.refl env body)))"
    );

    // beta: source app (lam A b0) arg — app /= lam.
    let beta_arm = concat!(
        "(fun (A : KExpr) (A' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_p env A A') (_hb0 : par_reduces_p env b0 b0') ",
        "(_harg : par_reduces_p env arg arg') ",
        "(_ihA : Eq KExpr A (KExpr.lam ty body) -> C A') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(_iharg : Eq KExpr arg (KExpr.lam ty body) -> C arg') ",
        "(eq : Eq KExpr (KExpr.app (KExpr.lam A b0) arg) (KExpr.lam ty body)) => ",
        "app_ne_lam (KExpr.lam A b0) arg ty body (C (instantiate b0' arg')) eq)"
    );

    // app: source app g b — app /= lam.
    let app_arm = concat!(
        "(fun (g : KExpr) (g' : KExpr) (b : KExpr) (b' : KExpr) ",
        "(_hg : par_reduces_p env g g') (_hb : par_reduces_p env b b') ",
        "(_ihg : Eq KExpr g (KExpr.lam ty body) -> C g') ",
        "(_ihb : Eq KExpr b (KExpr.lam ty body) -> C b') ",
        "(eq : Eq KExpr (KExpr.app g b) (KExpr.lam ty body)) => ",
        "app_ne_lam g b ty body (C (KExpr.app g' b')) eq)"
    );

    // lam: source lam t0 b0 — the matching congruence arm.
    let lam_arm = concat!(
        "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(ht : par_reduces_p env t0 t0') (hb : par_reduces_p env b0 b0') ",
        "(_iht : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
        "(_ihb : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.lam ty body)) => ",
        "klam t0' b0' ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x t0') t0 ty ",
        "(lam_inj_fst t0 b0 ty body eq) ht) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x b0') b0 body ",
        "(lam_inj_snd t0 b0 ty body eq) hb))"
    );

    // pi: source pi dom b0 — pi /= lam.
    let pi_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_p env dom dom') (_hb0 : par_reduces_p env b0 b0') ",
        "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> C dom') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.pi dom b0) (KExpr.lam ty body)) => ",
        "pi_ne_lam dom b0 ty body (C (KExpr.pi dom' b0')) eq)"
    );

    // forall_: source forall_ dom b0 = pi dom b0 (alias) — pi /= lam.
    let forall_arm = concat!(
        "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
        "(_hd : par_reduces_p env dom dom') (_hb0 : par_reduces_p env b0 b0') ",
        "(_ihd : Eq KExpr dom (KExpr.lam ty body) -> C dom') ",
        "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
        "(eq : Eq KExpr (KExpr.forall_ dom b0) (KExpr.lam ty body)) => ",
        "pi_ne_lam dom b0 ty body (C (KExpr.forall_ dom' b0')) eq)"
    );

    // let_ (ZETA): source let_ t0 v b0 (a genuine let, NEVER a lam) — refute the
    // source equation via the let/lam discriminator.
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> C v') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
            "Empty.rec (fun (_ : Empty) => C (instantiate b0' v')) ",
            "(Eq.substType KExpr {discr} (KExpr.let_ t0 v b0) (KExpr.lam ty body) eq Nat.zero))"
        ),
        discr = CD_KEXPR_NOT_LAM,
    );

    // let_cong (trailing CONGRUENCE): source let_ t0 v b0 (never a lam) — same
    // refutation, reduct KExpr.let_ t0' v' b0'.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.lam ty body) -> C t0') ",
            "(_ihv : Eq KExpr v (KExpr.lam ty body) -> C v') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.lam ty body) -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.lam ty body)) => ",
            "Empty.rec (fun (_ : Empty) => C (KExpr.let_ t0' v' b0')) ",
            "(Eq.substType KExpr {discr} (KExpr.let_ t0 v b0) (KExpr.lam ty body) eq Nat.zero))"
        ),
        discr = CD_KEXPR_NOT_LAM,
    );

    // iota_p: source e0 ⇒_p e2 then iota_step e2 r. The iota fires on e2, NOT e0.
    // e2 is a par-reduct of (lam ty body) (transport hprem along eq), so by
    // par_reduces_p_lam_reduct_not_redex it is not a redex — discharging the fired
    // iota on e2 and yielding C r directly.
    let iota_arm = concat!(
        "(fun (e0 : KExpr) (e2 : KExpr) (r : KExpr) ",
        "(hprem : par_reduces_p env e0 e2) (hi : iota_step env e2 r) ",
        "(_ihprem : Eq KExpr e0 (KExpr.lam ty body) -> C e2) ",
        "(eq : Eq KExpr e0 (KExpr.lam ty body)) => ",
        "par_reduces_p_lam_reduct_not_redex env ty body e2 r (C r) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x e2) e0 (KExpr.lam ty body) eq hprem) ",
        "hi)"
    );

    // proj arm: source proj s i sub is proj-headed — proj /= lam via proj_ne_lam.
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_p env sub sub') ",
        "(_ihsub : Eq KExpr sub (KExpr.lam ty body) -> C sub') ",
        "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam ty body)) => ",
        "proj_ne_lam s i sub ty body (C (KExpr.proj s i sub')) eq)"
    );

    format!(
        concat!(
            "fun (env : RecEnv) (ty : KExpr) (body : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_p env (KExpr.lam ty body) t) ",
            "(klam : forall (ty' : KExpr) (body' : KExpr), ",
            "par_reduces_p env ty ty' -> par_reduces_p env body body' -> ",
            "C (KExpr.lam ty' body')) => ",
            "par_reduces_p.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.lam ty body) t h (Eq.refl KExpr (KExpr.lam ty body))"
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
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// The three continuation types of `par_reduces_p_app_inv` (shared by the type and
/// the source-equation motive). `f`, `a`, `C` are the fixed outer parameters.
fn app_inv_kont_tys() -> (String, String, String) {
    let kcong = concat!(
        "(forall (f' : KExpr) (a' : KExpr), ",
        "par_reduces_p env f f' -> par_reduces_p env a a' -> C (KExpr.app f' a'))"
    )
    .to_string();
    let kbeta = concat!(
        "(forall (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg' : KExpr), ",
        "Eq KExpr f (KExpr.lam A body) -> ",
        "par_reduces_p env A A' -> par_reduces_p env body body' -> par_reduces_p env a arg' -> ",
        "C (instantiate body' arg'))"
    )
    .to_string();
    let kiota = concat!(
        "(forall (e2 : KExpr) (r : KExpr), ",
        "par_reduces_p env (KExpr.app f a) e2 -> iota_step env e2 r -> C r)"
    )
    .to_string();
    (kcong, kbeta, kiota)
}

/// Type of `par_reduces_p_app_inv`.
fn par_reduces_p_app_inv_type() -> String {
    let (kcong, kbeta, kiota) = app_inv_kont_tys();
    format!(
        "forall (env : RecEnv) (f : KExpr) (a : KExpr) (t : KExpr) (C : KExpr -> Type), \
         par_reduces_p env (KExpr.app f a) t -> \
         {kcong} -> {kbeta} -> {kiota} -> C t"
    )
}

/// Closed proof term for `par_reduces_p_app_inv` (Target #1). Mirrors
/// `par_reduces_c_app_inv_proof` over `par_reduces_p` (env threaded), with the
/// genuine-new PARALLEL-iota arm: the iota_p constructor fires on the REDUCED premise
/// `e0 ⇒_p e2` (then `iota_step e2 r`), so the kiota continuation carries the
/// intermediate `e2` and the transported premise `(app f a) ⇒_p e2`, NOT a bare
/// `iota_step env (app f a) t`. Single `par_reduces_p.rec` with a source-equation
/// motive `Eq KExpr e (app f a) -> kcong -> kbeta -> kiota -> C e'`; binder arms
/// discharge via lam_ne_app / pi_ne_app no-confusion on the source equation.
fn par_reduces_p_app_inv_proof() -> String {
    let (kcong_ty, kbeta_ty, kiota_ty) = app_inv_kont_tys();
    // Motive M e e' _h := Eq KExpr e (app f a) -> kcong -> kbeta -> kiota -> C e'.
    let motive = format!(
        "(fun (e : KExpr) (e' : KExpr) (_h : par_reduces_p env e e') => \
         Eq KExpr e (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C e')"
    );
    // The per-arm continuation-binder prefix (kc / kb / ki of the motive types).
    let konts = format!("(kc : {kcong_ty}) (kb : {kbeta_ty}) (ki : {kiota_ty})");

    // refl arm: reduct is e itself; rewrite e -> app f a, deliver via kc.
    // After the source equation eq : e = app f a, kc f a (refl f)(refl a) : C (app f a);
    // transport C (app f a) -> C e via Eq.symm eq.
    let refl_arm = format!(
        concat!(
            "(fun (e : KExpr) (eq : Eq KExpr e (KExpr.app f a)) {konts} => ",
            "Eq.substType KExpr C (KExpr.app f a) e ",
            "(Eq.symm KExpr e (KExpr.app f a) eq) ",
            "(kc f a (par_reduces_p.refl env f) (par_reduces_p.refl env a)))"
        ),
        konts = konts,
    );

    // beta arm: source app (lam A0 b0) arg ⇒_p instantiate b0' arg'. The source IS
    // app-headed (head = lam A0 b0, arg = arg), so app_inj recovers f = lam A0 b0 and
    // a = arg from eq. Feed kb A0 A0' b0 b0' arg' with f = lam A0 b0 (symm app_inj_fst)
    // and the a-side reduction transported (arg ⇒_p arg' becomes a ⇒_p arg' via
    // app_inj_snd : arg = a). Verbatim mirror of par_reduces_bd_app_inv's beta arm.
    let beta_arm = format!(
        concat!(
            "(fun (A0 : KExpr) (A0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(arg : KExpr) (arg' : KExpr) ",
            "(hA : par_reduces_p env A0 A0') (hb0 : par_reduces_p env b0 b0') ",
            "(harg : par_reduces_p env arg arg') ",
            "(_ihA : Eq KExpr A0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C A0') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C b0') ",
            "(_iharg : Eq KExpr arg (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C arg') ",
            "(eq : Eq KExpr (KExpr.app (KExpr.lam A0 b0) arg) (KExpr.app f a)) {konts} => ",
            "kb A0 A0' b0 b0' arg' ",
            "(Eq.symm KExpr (KExpr.lam A0 b0) f ",
            "(app_inj_fst (KExpr.lam A0 b0) arg f a eq)) ",
            "hA hb0 ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x arg') arg a ",
            "(app_inj_snd (KExpr.lam A0 b0) arg f a eq) harg))"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        konts = konts,
    );

    // app arm: source app g0 b ⇒_p app g0' b'. app_inj recovers g0 = f, b = a; feed kc
    // with the reductions transported along those equalities (g0 ⇒_p g0' becomes
    // f ⇒_p g0', b ⇒_p b' becomes a ⇒_p b'). Verbatim mirror of the bd app arm.
    let app_arm = format!(
        concat!(
            "(fun (g0 : KExpr) (g0' : KExpr) (b : KExpr) (b' : KExpr) ",
            "(hg : par_reduces_p env g0 g0') (hb : par_reduces_p env b b') ",
            "(_ihg : Eq KExpr g0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C g0') ",
            "(_ihb : Eq KExpr b (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C b') ",
            "(eq : Eq KExpr (KExpr.app g0 b) (KExpr.app f a)) {konts} => ",
            "kc g0' b' ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x g0') g0 f ",
            "(app_inj_fst g0 b f a eq) hg) ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x b') b a ",
            "(app_inj_snd g0 b f a eq) hb))"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        konts = konts,
    );

    // lam arm: source lam t0 b0 — lam /= app, discharge via lam_ne_app on eq.
    let lam_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_ht : par_reduces_p env t0 t0') (_hb : par_reduces_p env b0 b0') ",
            "(_iht : Eq KExpr t0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C t0') ",
            "(_ihb : Eq KExpr b0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C b0') ",
            "(eq : Eq KExpr (KExpr.lam t0 b0) (KExpr.app f a)) {konts} => ",
            "lam_ne_app t0 b0 f a (C (KExpr.lam t0' b0')) eq)"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        konts = konts,
    );

    // pi arm: source pi dom b0 — pi /= app, discharge via pi_ne_app on eq.
    let pi_arm = format!(
        concat!(
            "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_p env dom dom') (_hb0 : par_reduces_p env b0 b0') ",
            "(_ihd : Eq KExpr dom (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C dom') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C b0') ",
            "(eq : Eq KExpr (KExpr.pi dom b0) (KExpr.app f a)) {konts} => ",
            "pi_ne_app dom b0 f a (C (KExpr.pi dom' b0')) eq)"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        konts = konts,
    );

    // forall_ arm: source forall_ dom b0 = pi dom b0 (alias) — pi /= app.
    let forall_arm = format!(
        concat!(
            "(fun (dom : KExpr) (dom' : KExpr) (b0 : KExpr) (b0' : KExpr) ",
            "(_hd : par_reduces_p env dom dom') (_hb0 : par_reduces_p env b0 b0') ",
            "(_ihd : Eq KExpr dom (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C dom') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C b0') ",
            "(eq : Eq KExpr (KExpr.forall_ dom b0) (KExpr.app f a)) {konts} => ",
            "pi_ne_app dom b0 f a (C (KExpr.forall_ dom' b0')) eq)"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        konts = konts,
    );

    // let_ (ZETA) arm: source let_ t0 v b0 — a GENUINE let is never app-headed (under
    // the retired alias it literally was app (lam t0 b0) v and fed kb; no longer).
    // Refute the source equation via the let/app discriminator.
    let let_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C t0') ",
            "(_ihv : Eq KExpr v (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C v') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.app f a)) {konts} => ",
            "Empty.rec (fun (_ : Empty) => C (instantiate b0' v')) ",
            "(Eq.substType KExpr {discr} (KExpr.let_ t0 v b0) (KExpr.app f a) eq Nat.zero))"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        konts = konts,
        discr = CD_KEXPR_NOT_APP,
    );

    // let_cong (trailing CONGRUENCE) arm: source let_ t0 v b0 (never app-headed) —
    // same refutation, reduct KExpr.let_ t0' v' b0'.
    let let_cong_arm = format!(
        concat!(
            "(fun (t0 : KExpr) (t0' : KExpr) (v : KExpr) (v' : KExpr) ",
            "(b0 : KExpr) (b0' : KExpr) ",
            "(_ht0 : par_reduces_p env t0 t0') (_hv : par_reduces_p env v v') ",
            "(_hb0 : par_reduces_p env b0 b0') ",
            "(_iht0 : Eq KExpr t0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C t0') ",
            "(_ihv : Eq KExpr v (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C v') ",
            "(_ihb0 : Eq KExpr b0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C b0') ",
            "(eq : Eq KExpr (KExpr.let_ t0 v b0) (KExpr.app f a)) {konts} => ",
            "Empty.rec (fun (_ : Empty) => C (KExpr.let_ t0' v' b0')) ",
            "(Eq.substType KExpr {discr} (KExpr.let_ t0 v b0) (KExpr.app f a) eq Nat.zero))"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        konts = konts,
        discr = CD_KEXPR_NOT_APP,
    );

    // iota_p arm: source e0 ⇒_p e2 then iota_step e2 r0, reduct r0. Given eq : e0 =
    // app f a, transport the premise hprem : e0 ⇒_p e2 to (app f a) ⇒_p e2, then feed
    // ki e2 r0 <transported premise> hi0 : C r0. The IH is unused (the kiota
    // continuation does not recurse — the reduct r0 is delivered directly).
    let iota_arm = format!(
        concat!(
            "(fun (e0 : KExpr) (e2 : KExpr) (r0 : KExpr) ",
            "(hprem : par_reduces_p env e0 e2) (hi0 : iota_step env e2 r0) ",
            "(_ihprem : Eq KExpr e0 (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C e2) ",
            "(eq : Eq KExpr e0 (KExpr.app f a)) {konts} => ",
            "ki e2 r0 ",
            "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env x e2) e0 (KExpr.app f a) eq hprem) ",
            "hi0)"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        konts = konts,
    );

    // proj arm: source proj s i sub (never app-headed) — refute via the inline
    // not-app discriminator, same as the let_/let_cong arms.
    let proj_arm = format!(
        concat!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
            "(_hsub : par_reduces_p env sub sub') ",
            "(_ihsub : Eq KExpr sub (KExpr.app f a) -> {kcong_ty} -> {kbeta_ty} -> {kiota_ty} -> C sub') ",
            "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.app f a)) {konts} => ",
            "Empty.rec (fun (_ : Empty) => C (KExpr.proj s i sub')) ",
            "(Eq.substType KExpr {discr} (KExpr.proj s i sub) (KExpr.app f a) eq Nat.zero))"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        konts = konts,
        discr = CD_KEXPR_NOT_APP,
    );

    format!(
        concat!(
            "fun (env : RecEnv) (f : KExpr) (a : KExpr) (t : KExpr) (C : KExpr -> Type) ",
            "(h : par_reduces_p env (KExpr.app f a) t) ",
            "(kc : {kcong_ty}) (kb : {kbeta_ty}) (ki : {kiota_ty}) => ",
            "par_reduces_p.rec env {motive} ",
            "{refl_arm} {beta_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} ",
            "(KExpr.app f a) t h (Eq.refl KExpr (KExpr.app f a)) kc kb ki"
        ),
        kcong_ty = kcong_ty,
        kbeta_ty = kbeta_ty,
        kiota_ty = kiota_ty,
        motive = motive,
        refl_arm = refl_arm,
        beta_arm = beta_arm,
        app_arm = app_arm,
        lam_arm = lam_arm,
        pi_arm = pi_arm,
        forall_arm = forall_arm,
        let_arm = let_arm,
        iota_arm = iota_arm,
        let_cong_arm = let_cong_arm,
        proj_arm = proj_arm,
    )
}

/// Closed proof term for `cd_refl` (L1b): `par_reduces_p env e (cd env e)`. Structural
/// `KExpr.rec` on `e`; the app arm is the crux (kexpr_lam_cases split + OptionType
/// convoy + L1a inversion for the beta component reductions). See the registration
/// comment for the per-arm plan.
fn cd_refl_proof() -> String {
    // Motive: M e = par_reduces_p env e (cd env e).
    let motive = "(fun (e : KExpr) => par_reduces_p env e (cd env e))";

    // sort/bvar/const: cd is the identity here (cd (sort n) = sort n etc., by refl).
    let sort_arm = "(fun (n : Level) => par_reduces_p.refl env (KExpr.sort n))";
    let bvar_arm = "(fun (i : Nat) => par_reduces_p.refl env (KExpr.bvar i))";
    let const_arm =
        "(fun (nm : Name) (us : ListType Level) => par_reduces_p.refl env (KExpr.const nm us))";

    // lam/pi binder arm: cd env (HEAD ty b) = HEAD (cd ty)(cd b) (cd_lam/cd_pi). The
    // par_reduces_p.HEAD congruence on the two IHs, transported to cd env (HEAD ty b).
    let binder_arm = |ctor: &str, head: &str, unfold: &str| -> String {
        format!(
            concat!(
                "(fun (ty : KExpr) (b : KExpr) ",
                "(ihty : par_reduces_p env ty (cd env ty)) (ihb : par_reduces_p env b (cd env b)) => ",
                "Eq.substType KExpr ",
                "(fun (x : KExpr) => par_reduces_p env ({head} ty b) x) ",
                "({head} (cd env ty) (cd env b)) (cd env ({head} ty b)) ",
                "(Eq.symm KExpr (cd env ({head} ty b)) ({head} (cd env ty) (cd env b)) ({unfold} env ty b)) ",
                "({ctor} env ty (cd env ty) b (cd env b) ihty ihb))"
            ),
            ctor = ctor,
            head = head,
            unfold = unfold,
        )
    };

    // ---- app arm ----
    // f a, ihf : M f, iha : M a. Goal: par_reduces_p env (app f a) (cd env (app f a)).
    // Split kexpr_lam_cases f into the beta branch (f = lam A b0) and the iota/app
    // branch (kexpr_is_lam f = false).
    let cdf = "(cd env f)";
    let cda = "(cd env a)";
    let dflt = "(KExpr.app (cd env f) (cd env a))";
    let opt = "(iota_reduct env (KExpr.app (cd env f) (cd env a)))";

    // app congruence on the two IHs: par_reduces_p env (app f a)(app cdf cda).
    let app_cong = "(par_reduces_p.app env f (cd env f) a (cd env a) ihf iha)";

    // FALSE branch (kexpr_is_lam f = false). Bridge cd env (app f a) to
    // opt_default opt dflt via cd_app + hfalse, then an OptionType convoy.
    // none arm: opt_default none dflt = dflt = app cdf cda  -> app congruence.
    let conv_none = format!(
        "(fun (eqn : Eq (OptionType KExpr) {opt} (OptionType.none KExpr)) => {app_cong})",
        opt = opt,
        app_cong = app_cong,
    );
    // some arm: opt_default (some r) dflt = r; eqn : opt = some r is iota_step env dflt r.
    let conv_some = format!(
        concat!(
            "(fun (r : KExpr) (eqn : Eq (OptionType KExpr) {opt} (OptionType.some KExpr r)) => ",
            "par_reduces_p.iota_p env (KExpr.app f a) {dflt} r {app_cong} eqn)"
        ),
        opt = opt,
        dflt = dflt,
        app_cong = app_cong,
    );
    // convoy motive over o : OptionType KExpr.
    let conv_motive = format!(
        concat!(
            "(fun (o : OptionType KExpr) => Eq (OptionType KExpr) {opt} o -> ",
            "par_reduces_p env (KExpr.app f a) (opt_default o {dflt}))"
        ),
        opt = opt,
        dflt = dflt,
    );
    // proof of par_reduces_p env (app f a) (opt_default opt dflt).
    let on_opt_default = format!(
        concat!(
            "(OptionType.rec KExpr {conv_motive} {conv_none} {conv_some} {opt} ",
            "(Eq.refl (OptionType KExpr) {opt}))"
        ),
        conv_motive = conv_motive,
        conv_none = conv_none,
        conv_some = conv_some,
        opt = opt,
    );
    // eq_cd : cd env (app f a) = opt_default opt dflt. cd_app gives the Bool.rec form;
    // hfalse rewrites (kexpr_is_lam f) -> Bool.false, computing to the false arm.
    let eq_cd = format!(
        concat!(
            "(Eq.subst Bool ",
            "(fun (bcond : Bool) => Eq KExpr (cd env (KExpr.app f a)) ",
            "(Bool.rec (fun (_ : Bool) => KExpr) ",
            "(opt_default {opt} {dflt}) ",
            "(instantiate (kexpr_lam_body {cdf}) {cda}) bcond)) ",
            "(kexpr_is_lam f) Bool.false hfalse ",
            "(cd_app env f a))"
        ),
        opt = opt,
        dflt = dflt,
        cdf = cdf,
        cda = cda,
    );
    let false_branch = format!(
        concat!(
            "(fun (hfalse : Eq Bool (kexpr_is_lam f) Bool.false) => ",
            "Eq.substType KExpr ",
            "(fun (x : KExpr) => par_reduces_p env (KExpr.app f a) x) ",
            "(opt_default {opt} {dflt}) (cd env (KExpr.app f a)) ",
            "(Eq.symm KExpr (cd env (KExpr.app f a)) (opt_default {opt} {dflt}) {eq_cd}) ",
            "{on_opt_default})"
        ),
        opt = opt,
        dflt = dflt,
        eq_cd = eq_cd,
        on_opt_default = on_opt_default,
    );

    // TRUE/LAM branch (f = lam A b0). Prove P(g) := par_reduces_p env (app g a)
    // (cd env (app g a)) at g = lam A b0, then Eq.subst back to f via hf.
    //
    // ihf transported to (lam A b0) ⇒_p cd env (lam A b0) = lam (cd A)(cd b0) (cd_lam).
    let ihf_lam = concat!(
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env (KExpr.lam A b0) x) ",
        "(cd env (KExpr.lam A b0)) (KExpr.lam (cd env A) (cd env b0)) ",
        "(cd_lam env A b0) ",
        "(Eq.substType KExpr (fun (g : KExpr) => par_reduces_p env g (cd env g)) ",
        "f (KExpr.lam A b0) hf ihf))"
    );
    let beta_goal =
        "(par_reduces_p env (KExpr.app (KExpr.lam A b0) a) (instantiate (cd env b0) (cd env a)))";
    // klam_inv ty2 body2 hty2 hbody2 zeq: rewrite ty2->cd A, body2->cd b0, build beta.
    let klam_inv = concat!(
        "(fun (ty2 : KExpr) (body2 : KExpr) ",
        "(hty2 : par_reduces_p env A ty2) (hbody2 : par_reduces_p env b0 body2) ",
        "(zeq : Eq KExpr (KExpr.lam ty2 body2) (KExpr.lam (cd env A) (cd env b0))) => ",
        "par_reduces_p.beta env A (cd env A) b0 (cd env b0) a (cd env a) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env A x) ty2 (cd env A) ",
        "(lam_inj_fst ty2 body2 (cd env A) (cd env b0) zeq) hty2) ",
        "(Eq.substType KExpr (fun (x : KExpr) => par_reduces_p env b0 x) body2 (cd env b0) ",
        "(lam_inj_snd ty2 body2 (cd env A) (cd env b0) zeq) hbody2) ",
        "iha)"
    );
    let p_lam = format!(
        concat!(
            "(Eq.substType KExpr ",
            "(fun (x : KExpr) => par_reduces_p env (KExpr.app (KExpr.lam A b0) a) x) ",
            "(instantiate (cd env b0) (cd env a)) (cd env (KExpr.app (KExpr.lam A b0) a)) ",
            "(Eq.symm KExpr (cd env (KExpr.app (KExpr.lam A b0) a)) (instantiate (cd env b0) (cd env a)) ",
            "(cd_app_lam env A b0 a)) ",
            "(par_reduces_p_lam_inv env A b0 (KExpr.lam (cd env A) (cd env b0)) ",
            "(fun (z : KExpr) => Eq KExpr z (KExpr.lam (cd env A) (cd env b0)) -> {beta_goal}) ",
            "{ihf_lam} {klam_inv} ",
            "(Eq.refl KExpr (KExpr.lam (cd env A) (cd env b0)))))"
        ),
        beta_goal = beta_goal,
        ihf_lam = ihf_lam,
        klam_inv = klam_inv,
    );
    let lam_branch = format!(
        concat!(
            "(fun (A : KExpr) (b0 : KExpr) (hf : Eq KExpr f (KExpr.lam A b0)) => ",
            "Eq.substType KExpr ",
            "(fun (g : KExpr) => par_reduces_p env (KExpr.app g a) (cd env (KExpr.app g a))) ",
            "(KExpr.lam A b0) f ",
            "(Eq.symm KExpr f (KExpr.lam A b0) hf) ",
            "{p_lam})"
        ),
        p_lam = p_lam,
    );

    let app_arm = format!(
        concat!(
            "(fun (f : KExpr) (a : KExpr) ",
            "(ihf : par_reduces_p env f (cd env f)) (iha : par_reduces_p env a (cd env a)) => ",
            "kexpr_lam_cases f (par_reduces_p env (KExpr.app f a) (cd env (KExpr.app f a))) ",
            "{lam_branch} {false_branch})"
        ),
        lam_branch = lam_branch,
        false_branch = false_branch,
    );

    // let_ arm (genuine 7th ctor): cd fires the top zeta — cd env (let_ ty val body) =
    // instantiate (cd body)(cd val) (cd_let), delivered by par_reduces_p.let_ (zeta) on
    // the three IHs, transported to cd env (let_ ty val body). Beta-branch shape.
    let let_arm = concat!(
        "(fun (ty : KExpr) (val : KExpr) (body : KExpr) ",
        "(ihty : par_reduces_p env ty (cd env ty)) ",
        "(ihval : par_reduces_p env val (cd env val)) ",
        "(ihbody : par_reduces_p env body (cd env body)) => ",
        "Eq.substType KExpr ",
        "(fun (x : KExpr) => par_reduces_p env (KExpr.let_ ty val body) x) ",
        "(instantiate (cd env body) (cd env val)) (cd env (KExpr.let_ ty val body)) ",
        "(Eq.symm KExpr (cd env (KExpr.let_ ty val body)) (instantiate (cd env body) (cd env val)) ",
        "(cd_let env ty val body)) ",
        "(par_reduces_p.let_ env ty (cd env ty) val (cd env val) body (cd env body) ihty ihval ihbody))"
    );

    // proj arm: cd descends into the scrutinee (cd env (proj s i sub) = proj s i
    // (cd env sub) by defeq); congruence via par_reduces_p.proj on the IH.
    let proj_arm = concat!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) ",
        "(ihsub : par_reduces_p env sub (cd env sub)) => ",
        "par_reduces_p.proj env s i sub (cd env sub) ihsub)"
    );

    // lit arm: cd env (lit v) = lit v (defeq); reflexive par-step.
    let lit_arm = "(fun (v : Nat) => par_reduces_p.refl env (KExpr.lit v))";

    format!(
        concat!(
            "fun (env : RecEnv) (e0 : KExpr) => ",
            "KExpr.rec {motive} ",
            "{sort_arm} {bvar_arm} {app_arm} ",
            "{lam_arm} {pi_arm} {const_arm} {let_arm} {proj_arm} {lit_arm} ",
            "e0"
        ),
        motive = motive,
        sort_arm = sort_arm,
        bvar_arm = bvar_arm,
        app_arm = app_arm,
        lam_arm = binder_arm("par_reduces_p.lam", "KExpr.lam", "cd_lam"),
        pi_arm = binder_arm("par_reduces_p.pi", "KExpr.pi", "cd_pi"),
        const_arm = const_arm,
        let_arm = let_arm,
        proj_arm = proj_arm,
        lit_arm = lit_arm,
    )
}

// =====================================================================
// L2 core: par_reduces_p_reduct_cong_spine — the structural-args iota
// reduct congruence (design §11). The iota reduct is a 3-layer apply_spine:
//   reduct(e) = apply_spine (extras)
//                 (apply_spine (fields over major)
//                   (apply_spine (prefix) rhs))
// where (from the redex boundary meta/rule):
//   major_idx = params + motives + minors + indices
//   prefix_n  = params + motives + minors
//   extras    = list_drop (succ major_idx) (kapp_args e)
//   fields    = list_drop (len (kapp_args major) - num_fields) (kapp_args major)
//   prefix    = list_take prefix_n (kapp_args e)
// The (app f a)-side uses the generic major in the fields layer; the
// (app f' a')-side uses a'. Given the two spine congruences as hypotheses,
// each layer par-reduces (apply_spine_par_p over list_drop_par_p /
// list_take_par_p), so the two reducts par-reduce. Direct c→p port of
// par_reduces_c_reduct_cong's apply_spine assembly.
// =====================================================================

/// Shared sub-term builders for `par_reduces_p_reduct_cong_spine` (verbatim
/// from `iota_reduct`'s reduct shape).
fn reduct_cong_spine_pieces() -> (String, String, String, String) {
    let major_idx = "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))".to_string();
    let prefix_n = "(Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta))".to_string();
    let nf = "(recrule_num_fields rule)".to_string();
    let p_rhs = "(recrule_rhs rule)".to_string();
    (major_idx, prefix_n, nf, p_rhs)
}

/// The (app f a)-side iota reduct (`R_fa`, generic `major` in the fields layer)
/// and the (app f' a')-side reduct (`reduct_m`, `a'` in the fields layer).
fn reduct_cong_spine_reducts() -> (String, String) {
    let (major_idx, prefix_n, nf, p_rhs) = reduct_cong_spine_pieces();
    let kargs_fa = "(kapp_args (KExpr.app f a))";
    let kargs_fap = "(kapp_args (KExpr.app f' a'))";
    let r_fa = format!(
        "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_fa}) \
         (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) {nf}) (kapp_args major)) \
         (apply_spine (list_take {prefix_n} {kargs_fa}) {p_rhs})))"
    );
    let reduct_m = format!(
        "(apply_spine (list_drop (Nat.succ {major_idx}) {kargs_fap}) \
         (apply_spine (list_drop (Nat.sub (list_length (kapp_args a')) {nf}) (kapp_args a')) \
         (apply_spine (list_take {prefix_n} {kargs_fap}) {p_rhs})))"
    );
    (r_fa, reduct_m)
}

/// `major_idx(meta)` for the assembled minimal reduct cong (same arithmetic as
/// `reduct_cong_spine_pieces` / `spine_below_major_idx`, here in terms of the `meta`
/// binder of `par_reduces_p_reduct_cong`).
fn reduct_cong_major_idx() -> String {
    "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))".to_string()
}

/// Type of `par_reduces_p_reduct_cong` — the assembled minimal (LEFT-leg) reduct
/// congruence. Mirrors the c-side `par_reduces_c_reduct_cong` (D.3) type with `_p`
/// and the sharpened disjointness interface `RecEnvCtorNoRecMeta` replacing the c-side
/// not-redex guards. The reducts `e1` (LHS, via `h5r`) and `reduct_m` (RHS) reuse
/// `reduct_cong_spine_reducts()`.
fn par_reduces_p_reduct_cong_type() -> String {
    let (r_fa, reduct_m) = reduct_cong_spine_reducts();
    format!(
        "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (e1 : KExpr) \
         (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
         RecEnvCtorNoRecMeta env -> \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) -> \
         Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
         Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
         Eq (OptionType KExpr) (OptionType.some KExpr {r_fa}) (OptionType.some KExpr e1) -> \
         Eq KExpr major a -> \
         Eq Nat {major_idx} (list_length (kapp_args f)) -> \
         par_reduces_p env f f' -> par_reduces_p env a a' -> \
         par_reduces_p env e1 {reduct_m}",
        major_idx = reduct_cong_major_idx(),
    )
}

/// Closed proof term for `par_reduces_p_reduct_cong`. Builds the f-spine (below-
/// boundary, recursor head) and major-spine (no-recmeta, constructor head via the
/// interface) congruences, feeds `par_reduces_p_reduct_cong_spine`, and transports the
/// source from `R_fa` to `e1` via `h5r`/`option_some_inj`.
fn par_reduces_p_reduct_cong_proof() -> String {
    let (r_fa, _reduct_m) = reduct_cong_spine_reducts();
    let major_idx = reduct_cong_major_idx();
    let len_f = "(list_length (kapp_args f))";

    // head f = some recname (h1-over-(app f a) lifted to f via kapp_fn_app).
    let head_f = "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) \
         (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) \
         (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) \
         (kapp_fn f) (kapp_fn (KExpr.app f a)) \
         (Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1)";

    // head a = some cname (h4 over major transported along hbnd : major = a).
    let head_a = "(Eq.subst KExpr \
         (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name cname)) \
         major a hbnd h4)";

    // BELOW-BOUNDARY guard Le (len(kapp_args f)) major_idx: reflexive via hidx
    // (major_idx = len(kapp_args f)). Le.refl len : Le len len; transport the SECOND
    // argument len -> major_idx along (Eq.symm hidx : len = major_idx). Le is a Prop
    // -> Eq.subst.
    let le_guard = format!(
        "(Eq.subst Nat (fun (z : Nat) => Le {len_f} z) {len_f} {major_idx} \
         (Eq.symm Nat {major_idx} {len_f} hidx) (Le.refl {len_f}))"
    );

    // f-spine congruence: kapp_args f ⇒_p_list kapp_args f' (recursor head, below boundary).
    let f_spine = format!(
        "(par_reduces_p_spine_cong_below_boundary env f f' recname meta {head_f} h2 {le_guard} hf)"
    );

    // whole-app spine congruence: kapp_args(app f a) ⇒_p_list kapp_args(app f' a').
    let whole_spine = format!("(kapp_args_par_p env f f' a a' {f_spine} ha)");

    // recmeta_for cname = none from the sharpened disjointness interface.
    let recmeta_none =
        "(recenv_ctor_no_recmeta_cname env recname cname rule major disjoint h4 h5)".to_string();

    // major/a-spine congruence: kapp_args a ⇒_p_list kapp_args a' (constructor head).
    let a_spine =
        format!("(par_reduces_p_spine_cong_no_recmeta env a a' cname {head_a} {recmeta_none} ha)");

    // Transport the source list kapp_args a -> kapp_args major via Eq.symm hbnd, so it
    // matches par_reduces_p_reduct_cong_spine's second hyp (over kapp_args major).
    let major_spine = format!(
        "(Eq.substType KExpr \
         (fun (Z : KExpr) => par_reduces_p_list env (kapp_args Z) (kapp_args a')) \
         a major (Eq.symm KExpr major a hbnd) {a_spine})"
    );

    // Assemble via the apply_spine reduct cong: par_reduces_p R_fa reduct_m.
    let assembled = format!(
        "(par_reduces_p_reduct_cong_spine env f f' a a' major meta rule {whole_spine} {major_spine} hbnd)"
    );

    // Recover e1 = R_fa from h5r (option_some_inj) and transport the SOURCE.
    let r_fa_eq_e1 = format!("(option_some_inj KExpr {r_fa} e1 h5r)");
    let body = {
        let (_r, reduct_m) = reduct_cong_spine_reducts();
        format!(
            "Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env Z {reduct_m}) \
             {r_fa} e1 {r_fa_eq_e1} {assembled}"
        )
    };

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (e1 : KExpr) \
         (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
         (disjoint : RecEnvCtorNoRecMeta env) \
         (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
         (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
         (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
         (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
         (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {r_fa}) (OptionType.some KExpr e1)) \
         (hbnd : Eq KExpr major a) \
         (hidx : Eq Nat {major_idx} {len_f}) \
         (hf : par_reduces_p env f f') (ha : par_reduces_p env a a') => \
         {body}"
    )
}

/// Type of `par_reduces_p_app_redex` — the p-side (iota,app) minimal-join reduct
/// RECONSTRUCTION. Given the boundary-inverter witnesses for an iota redex (app f a)
/// (head/meta/major/cname/rule + hbnd : major = a + hidx : major_idx = len(kapp_args f)),
/// the sharpened disjointness interface, and the originals f ⇒_p f' / a ⇒_p a', it
/// delivers `iota_reduct env (app f' a') = some reduct_m` (the a'-side reduct). The p-side
/// analogue of the c-side `iota_reduct_par_app_redex`; with `par_reduces_p_reduct_cong`'s
/// LEFT leg (r0 ⇒_p reduct_m) + `iota_step_deterministic`, this pins the GIVEN opaque
/// (app f' a')-reduct rm0 to reduct_m.
fn par_reduces_p_app_redex_type() -> String {
    let (_r_fa, reduct_m) = reduct_cong_spine_reducts();
    let major_idx = reduct_cong_major_idx();
    format!(
        "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule), \
         RecEnvCtorNoRecMeta env -> \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) -> \
         Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname) -> \
         Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule) -> \
         Eq KExpr major a -> \
         Eq Nat {major_idx} (list_length (kapp_args f)) -> \
         par_reduces_p env f f' -> par_reduces_p env a a' -> \
         Eq (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr {reduct_m})"
    )
}

/// Closed proof term for `par_reduces_p_app_redex`. Mirror of the c-side
/// `iota_reduct_par_app_redex` glue (par_reduces_c.rs ~2146), reconstructing the five
/// (app f' a')-side lookups from the boundary witnesses + the par steps, then feeding
/// `iota_reduct_par_app_recon` (which is par_reduces_c-free — reused verbatim):
///   * hL1 head(app f' a') = some recname — `head f' = some recname` via the p-side
///     `par_reduces_p_preserves_head_const_below_boundary` (the below-boundary guard
///     reflexive via hidx), lifted by kapp_fn_app;
///   * h2 reused;
///   * hL3 list_head (list_drop major_idx (kapp_args (app f' a'))) = some a' — the major
///     sits at the boundary because len(kapp_args f) = len(kapp_args f')
///     (par_reduces_p_list_length_eq on the f-spine congruence), so list_head_drop_len_append
///     on kapp_args f' locates a';
///   * hL4 head a' = some cname — `head a = some cname` (h4 over major via hbnd) lifted by
///     the p-side `par_reduces_p_preserves_head_const_no_recmeta` (no-recmeta guard from
///     `recenv_ctor_no_recmeta_cname`);
///   * h5 reused.
fn par_reduces_p_app_redex_proof() -> String {
    let major_idx = reduct_cong_major_idx();
    let len_f = "(list_length (kapp_args f))";
    let len_fp = "(list_length (kapp_args f'))";
    let kargs_fap = "(kapp_args (KExpr.app f' a'))";
    let kargs_fap_snoc =
        "(list_append (kapp_args f') (ListType.cons KExpr a' (ListType.nil KExpr)))";

    // head f = some recname (h1-over-(app f a) lifted to f via kapp_fn_app).
    let head_f = "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) \
         (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname) \
         (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) \
         (kapp_fn f) (kapp_fn (KExpr.app f a)) \
         (Eq.symm KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a))) h1)";

    // BELOW-BOUNDARY guard Le (len(kapp_args f)) major_idx: reflexive via hidx.
    let le_guard = format!(
        "(Eq.subst Nat (fun (z : Nat) => Le {len_f} z) {len_f} {major_idx} \
         (Eq.symm Nat {major_idx} {len_f} hidx) (Le.refl {len_f}))"
    );

    // f-spine congruence: kapp_args f ⇒_p_list kapp_args f' (recursor head, below boundary).
    let f_spine = format!(
        "(par_reduces_p_spine_cong_below_boundary env f f' recname meta {head_f} h2 {le_guard} hf)"
    );
    // Spine-length stability: len(kapp_args f) = len(kapp_args f').
    let len_eq_ff =
        format!("(par_reduces_p_list_length_eq env (kapp_args f) (kapp_args f') {f_spine})");

    // hL1: head (app f' a') = some recname (head f' lifted via kapp_fn_app).
    let head_fp = format!(
        "(par_reduces_p_preserves_head_const_below_boundary env f f' recname meta {head_f} h2 {le_guard} hf)"
    );
    let h_l1 = format!(
        "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f' a'))) (kexpr_const_name (kapp_fn f')) (OptionType.some Name recname) \
         (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn (KExpr.app f' a')) (kapp_fn f') (kapp_fn_app f' a')) \
         {head_fp})"
    );

    // hL3: head (drop major_idx (kapp_args (app f' a'))) = some a'. Boundary identity for
    // f': major_idx = len(kapp_args f) = len(kapp_args f').
    let hidx_fp = format!("(Eq.trans Nat {major_idx} {len_f} {len_fp} hidx {len_eq_ff})");
    let bd_head = "(list_head_drop_len_append (kapp_args f') a')";
    let bd_head_at_idx = format!(
        "(Eq.subst Nat (fun (z : Nat) => Eq (OptionType KExpr) (list_head (list_drop z {kargs_fap_snoc})) (OptionType.some KExpr a')) \
         {len_fp} {major_idx} (Eq.symm Nat {major_idx} {len_fp} {hidx_fp}) {bd_head})"
    );
    let h_l3 = format!(
        "(Eq.subst (ListType KExpr) (fun (L : ListType KExpr) => Eq (OptionType KExpr) (list_head (list_drop {major_idx} L)) (OptionType.some KExpr a')) \
         {kargs_fap_snoc} {kargs_fap} \
         (Eq.symm (ListType KExpr) {kargs_fap} {kargs_fap_snoc} (kapp_args_app f' a')) \
         {bd_head_at_idx})"
    );

    // head a = some cname (h4 over major transported along hbnd : major = a).
    let head_a = "(Eq.subst KExpr \
         (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name cname)) \
         major a hbnd h4)";
    // recmeta_for cname = none from the sharpened disjointness interface.
    let recmeta_none =
        "(recenv_ctor_no_recmeta_cname env recname cname rule major disjoint h4 h5)".to_string();
    // hL4: head a' = some cname (head a lifted by the no-recmeta head preservation on a⇒a').
    let h_l4 = format!(
        "(par_reduces_p_preserves_head_const_no_recmeta env a a' cname {head_a} {recmeta_none} ha)"
    );

    // Feed iota_reduct_par_app_recon the five (app f' a')-side lookups.
    let recon = format!(
        "(iota_reduct_par_app_recon env f' a' recname meta cname rule {h_l1} h2 {h_l3} {h_l4} h5)"
    );

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
         (disjoint : RecEnvCtorNoRecMeta env) \
         (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
         (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
         (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
         (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
         (hbnd : Eq KExpr major a) \
         (hidx : Eq Nat {major_idx} {len_f}) \
         (hf : par_reduces_p env f f') (ha : par_reduces_p env a a') => \
         {recon}"
    )
}

/// Type of `par_reduces_p_app_reduct_cong_minimal` — the MINIMAL-case (f not a redex)
/// symmetric app reduct congruence. Given the minimal guard `iota_reduct env f = none`,
/// the disjointness interface, the originals f ⇒_p f' / a ⇒_p a', and BOTH endpoints as
/// iota redexes (`iota_step (app f a) r0`, `iota_step (app f' a') rm0`), the two reducts
/// join in `par_reduces_p_star`. This is the `happ`-shaped congruence for the boundary
/// case; the over-application case (f itself a redex) is routed through the keystone's
/// outer fuel IH, NOT this lemma.
fn par_reduces_p_app_reduct_cong_minimal_type() -> String {
    "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
     (r0 : KExpr) (rm0 : KExpr), \
     RecEnvCtorNoRecMeta env -> \
     Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr) -> \
     par_reduces_p env f f' -> par_reduces_p env a a' -> \
     iota_step env (KExpr.app f a) r0 -> iota_step env (KExpr.app f' a') rm0 -> \
     par_reduces_p_star env r0 rm0"
        .to_string()
}

/// Closed proof term for `par_reduces_p_app_reduct_cong_minimal`. Invert the GIVEN
/// `iota_step (app f a) r0` via `iota_reduct_app_minimal_boundary_idx_type` (C-type
/// `par_reduces_p_star env r0 rm0`). In the continuation (recname/meta/major/cname/rule +
/// h1/h2/h3/h4/h5/h5r/hbnd/hidx):
///   * LEFT leg `r0 ⇒_p reduct_m`: `par_reduces_p_reduct_cong` (recovers r0 = R_fa from
///     h5r; the reduct_m is the a'-side apply_spine).
///   * RIGHT pin `rm0 = reduct_m`: `par_reduces_p_app_redex` rebuilds
///     `iota_reduct (app f' a') = some reduct_m`, and `iota_step_deterministic` against
///     the GIVEN `iota_step (app f' a') rm0` forces `rm0 = reduct_m`.
///   * Transport `r0 ⇒_p reduct_m` along `Eq reduct_m rm0` (Eq.symm) into `r0 ⇒_p rm0`,
///     then subsume to `par_reduces_p_star` via `par_subsumes_par_p_star`.
fn par_reduces_p_app_reduct_cong_minimal_proof() -> String {
    let (_r_fa, reduct_m) = reduct_cong_spine_reducts();
    let star_goal = "(par_reduces_p_star env r0 rm0)";

    // The continuation handed to the boundary inverter (binders over (app f a)).
    let major_idx = reduct_cong_major_idx();
    let len_f = "(list_length (kapp_args f))";

    // LEFT leg: par_reduces_p env r0 reduct_m.
    let left_leg = "(par_reduces_p_reduct_cong env f f' a a' r0 recname meta major cname rule \
         disjoint h1 h2 h4 h5 h5r hbnd hidx hf ha)";
    // RIGHT reconstruction: iota_reduct env (app f' a') = some reduct_m.
    let right_recon = "(par_reduces_p_app_redex env f f' a a' recname meta major cname rule \
         disjoint h1 h2 h4 h5 hbnd hidx hf ha)";
    // rm0 = reduct_m via determinism on the GIVEN hrm0 + the reconstruction.
    let rm0_eq_reduct = format!(
        "(iota_step_deterministic env (KExpr.app f' a') rm0 {reduct_m} hrm0 {right_recon})"
    );
    // Transport r0 ⇒_p reduct_m along (Eq.symm : reduct_m = rm0) into r0 ⇒_p rm0.
    let r0_to_rm0 = format!(
        "(Eq.substType KExpr (fun (Z : KExpr) => par_reduces_p env r0 Z) {reduct_m} rm0 \
         (Eq.symm KExpr rm0 {reduct_m} {rm0_eq_reduct}) {left_leg})"
    );
    // Subsume to star.
    let star = format!("(par_subsumes_par_p_star env r0 rm0 {r0_to_rm0})");

    let kont = format!(
        "(fun (recname : Name) (meta : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule) \
         (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) \
         (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta)) \
         (h3 : Eq (OptionType KExpr) (list_head (list_drop {major_idx} (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) \
         (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (OptionType.some Name cname)) \
         (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) (OptionType.some RecRule rule)) \
         (h5r : Eq (OptionType KExpr) (OptionType.some KExpr {r_fa_app}) (OptionType.some KExpr r0)) \
         (hbnd : Eq KExpr major a) \
         (hidx : Eq Nat {major_idx} {len_f}) => \
         {star})",
        r_fa_app = reduct_cong_r_fa_app(),
    );

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (r0 : KExpr) (rm0 : KExpr) \
         (disjoint : RecEnvCtorNoRecMeta env) \
         (hfn : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) \
         (hf : par_reduces_p env f f') (ha : par_reduces_p env a a') \
         (hr0 : iota_step env (KExpr.app f a) r0) (hrm0 : iota_step env (KExpr.app f' a') rm0) => \
         iota_reduct_app_minimal_boundary_idx_type env f a r0 hr0 hfn {star_goal} {kont}"
    )
}

/// The (app f a)-side iota reduct `R_fa` over the GENERIC `major` binder (the reduct slot
/// the boundary inverter's `h5r` carries — matches `iota_reduct_app_minimal_boundary_idx_type`'s
/// `reduct_app` and `par_reduces_p_reduct_cong`'s LHS `R_fa`). Distinct from
/// `reduct_cong_spine_reducts().0` only in being kept as a standalone builder here.
fn reduct_cong_r_fa_app() -> String {
    let (r_fa, _reduct_m) = reduct_cong_spine_reducts();
    r_fa
}

/// Type of `par_reduces_p_reduct_cong_spine`.
fn par_reduces_p_reduct_cong_spine_type() -> String {
    let (r_fa, reduct_m) = reduct_cong_spine_reducts();
    format!(
        "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (major : KExpr) (meta : RecMeta) (rule : RecRule), \
         par_reduces_p_list env (kapp_args (KExpr.app f a)) (kapp_args (KExpr.app f' a')) -> \
         par_reduces_p_list env (kapp_args major) (kapp_args a') -> \
         Eq KExpr major a -> \
         par_reduces_p env {r_fa} {reduct_m}"
    )
}

/// Closed proof term for `par_reduces_p_reduct_cong_spine`. Mirror of the
/// apply_spine assembly inside `par_reduces_c_reduct_cong` (par_reduces_c.rs
/// ~2259), with the two `par_reduces_c_spine_cong` derivations replaced by the
/// hypotheses `hspine_whole` / `hspine_major`.
fn par_reduces_p_reduct_cong_spine_proof() -> String {
    let (major_idx, prefix_n, nf, p_rhs) = reduct_cong_spine_pieces();
    let kargs_fa = "(kapp_args (KExpr.app f a))";
    let kargs_fap = "(kapp_args (KExpr.app f' a'))";
    let major_drop_idx_maj = format!("(Nat.sub (list_length (kapp_args major)) {nf})");
    let major_drop_idx_ap = format!("(Nat.sub (list_length (kapp_args a')) {nf})");

    // Major's own spine congruence over major, with the SOURCE list transported
    // from kapp_args a (the hyp is stated over major directly, so this is just
    // hspine_major). Length stability: len(kapp_args major) = len(kapp_args a').
    let major_spine_cong = "hspine_major".to_string();
    let len_maj_eq_ap = format!(
        "(par_reduces_p_list_length_eq env (kapp_args major) (kapp_args a') {major_spine_cong})"
    );

    // Middle layer drop-congruence at the major-side index, then rewrite the
    // a'-side index from sub(len(kapp_args major))nf to sub(len(kapp_args a'))nf.
    let middle_drop_cong_majidx = format!(
        "(list_drop_par_p env {major_drop_idx_maj} (kapp_args major) (kapp_args a') {major_spine_cong})"
    );
    let sub_idx_eq = format!(
        "(Eq.cong Nat Nat (fun (N : Nat) => Nat.sub N {nf}) (list_length (kapp_args major)) (list_length (kapp_args a')) {len_maj_eq_ap})"
    );
    let middle_drop_cong = format!(
        "(Eq.substType Nat \
         (fun (Z : Nat) => par_reduces_p_list env (list_drop {major_drop_idx_maj} (kapp_args major)) (list_drop Z (kapp_args a'))) \
         {major_drop_idx_maj} {major_drop_idx_ap} {sub_idx_eq} \
         {middle_drop_cong_majidx})"
    );

    // Inner apply_spine: prefix layer (list_take prefix_n on both spines, rhs refl head).
    let prefix_take_cong =
        format!("(list_take_par_p env {prefix_n} {kargs_fa} {kargs_fap} hspine_whole)");
    let inner_spine = format!(
        "(apply_spine_par_p env (list_take {prefix_n} {kargs_fa}) (list_take {prefix_n} {kargs_fap}) {p_rhs} {p_rhs} {prefix_take_cong} (par_reduces_p.refl env {p_rhs}))"
    );

    // Middle apply_spine: fields layer over the inner spine head.
    let middle_spine = format!(
        "(apply_spine_par_p env (list_drop {major_drop_idx_maj} (kapp_args major)) (list_drop {major_drop_idx_ap} (kapp_args a')) \
         (apply_spine (list_take {prefix_n} {kargs_fa}) {p_rhs}) \
         (apply_spine (list_take {prefix_n} {kargs_fap}) {p_rhs}) \
         {middle_drop_cong} {inner_spine})"
    );

    // Outer apply_spine: extras layer over the middle spine head.
    let outer_drop_cong =
        format!("(list_drop_par_p env (Nat.succ {major_idx}) {kargs_fa} {kargs_fap} hspine_whole)");
    let outer_spine = format!(
        "(apply_spine_par_p env (list_drop (Nat.succ {major_idx}) {kargs_fa}) (list_drop (Nat.succ {major_idx}) {kargs_fap}) \
         (apply_spine (list_drop {major_drop_idx_maj} (kapp_args major)) (apply_spine (list_take {prefix_n} {kargs_fa}) {p_rhs})) \
         (apply_spine (list_drop {major_drop_idx_ap} (kapp_args a')) (apply_spine (list_take {prefix_n} {kargs_fap}) {p_rhs})) \
         {outer_drop_cong} {middle_spine})"
    );

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (major : KExpr) (meta : RecMeta) (rule : RecRule) \
         (hspine_whole : par_reduces_p_list env (kapp_args (KExpr.app f a)) (kapp_args (KExpr.app f' a'))) \
         (hspine_major : par_reduces_p_list env (kapp_args major) (kapp_args a')) \
         (hbnd : Eq KExpr major a) => \
         {outer_spine}"
    )
}

// =====================================================================
// L2 over-application arm (#2859 Increment F+, design §15(ii)):
// par_reduces_p_reduct_cong_over. The companion of the boundary-case
// par_reduces_p_reduct_cong_spine for the OVER-APPLICATION shape, where
// (app f a) is an iota redex whose major sits strictly inside f's spine — so
// f is itself a redex and the outer reduct is the inner reduct re-applied:
//   iota_reduct env (app f a) = some (app f1 a)   (via iota_reduct_app_some)
// with iota_reduct env f = some f1. Given the inner reduct congruence
// f1 ⇒_p f1' and a ⇒_p a', the two actual outer reducts e1 / m par-reduce by
// a single par_reduces_p.app, transported onto e1 / m. The c→p analogue of
// the c-side over-application identity iota_reduct_app_some (iota_core.rs).
// =====================================================================

/// Type of `par_reduces_p_reduct_cong_over`.
fn par_reduces_p_reduct_cong_over_type() -> String {
    "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
     (f1 : KExpr) (f1' : KExpr) (e1 : KExpr) (m : KExpr), \
     Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1) -> \
     Eq (OptionType KExpr) (iota_reduct env f') (OptionType.some KExpr f1') -> \
     Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1) -> \
     Eq (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr m) -> \
     par_reduces_p env f1 f1' -> \
     par_reduces_p env a a' -> \
     par_reduces_p env e1 m"
        .to_string()
}

/// Closed proof term for `par_reduces_p_reduct_cong_over`. Two `iota_reduct_app_some`
/// invocations rewrite both outer reducts to the over-application form `some (app
/// f1 a)` / `some (app f1' a')`; `option_some_inj` (after Eq.symm/Eq.trans against
/// the caller's `he1`/`hm`) pins `e1 = app f1 a` and `m = app f1' a'`; a single
/// `par_reduces_p.app` congruence on (f1 ⇒_p f1', a ⇒_p a') is transported onto
/// the actual outer reducts `e1` / `m` by `Eq.substType` (source then target).
fn par_reduces_p_reduct_cong_over_proof() -> String {
    // happ  : iota_reduct env (app f a)   = some (app f1 a)
    let happ = "(iota_reduct_app_some env f a f1 hf1)";
    // happ' : iota_reduct env (app f' a') = some (app f1' a')
    let happp = "(iota_reduct_app_some env f' a' f1' hf1')";

    // e1 = app f1 a (from happ, he1 via option_some_inj on some (app f1 a) = some e1).
    let some_appf1a_eq_some_e1 = format!(
        "(Eq.trans (OptionType KExpr) \
         (OptionType.some KExpr (KExpr.app f1 a)) \
         (iota_reduct env (KExpr.app f a)) \
         (OptionType.some KExpr e1) \
         (Eq.symm (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr (KExpr.app f1 a)) {happ}) \
         he1)"
    );
    let he1eq = format!("(option_some_inj KExpr (KExpr.app f1 a) e1 {some_appf1a_eq_some_e1})");

    // m = app f1' a' (from happ', hm via option_some_inj on some (app f1' a') = some m).
    let some_appf1pa_eq_some_m = format!(
        "(Eq.trans (OptionType KExpr) \
         (OptionType.some KExpr (KExpr.app f1' a')) \
         (iota_reduct env (KExpr.app f' a')) \
         (OptionType.some KExpr m) \
         (Eq.symm (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr (KExpr.app f1' a')) {happp}) \
         hm)"
    );
    let hmeq = format!("(option_some_inj KExpr (KExpr.app f1' a') m {some_appf1pa_eq_some_m})");

    // core : par_reduces_p env (app f1 a) (app f1' a').
    let core = "(par_reduces_p.app env f1 f1' a a' hpf1 hpa)".to_string();

    // Transport SOURCE (app f1 a -> e1): par_reduces_p env e1 (app f1' a').
    let core_src = format!(
        "(Eq.substType KExpr \
         (fun (Z : KExpr) => par_reduces_p env Z (KExpr.app f1' a')) \
         (KExpr.app f1 a) e1 {he1eq} {core})"
    );

    // Transport TARGET (app f1' a' -> m): par_reduces_p env e1 m.
    let body = format!(
        "(Eq.substType KExpr \
         (fun (Z : KExpr) => par_reduces_p env e1 Z) \
         (KExpr.app f1' a') m {hmeq} {core_src})"
    );

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) \
         (f1 : KExpr) (f1' : KExpr) (e1 : KExpr) (m : KExpr) \
         (hf1 : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr f1)) \
         (hf1' : Eq (OptionType KExpr) (iota_reduct env f') (OptionType.some KExpr f1')) \
         (he1 : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f a)) (OptionType.some KExpr e1)) \
         (hm : Eq (OptionType KExpr) (iota_reduct env (KExpr.app f' a')) (OptionType.some KExpr m)) \
         (hpf1 : par_reduces_p env f1 f1') \
         (hpa : par_reduces_p env a a') => \
         {body}"
    )
}

// =====================================================================
// L2 wall (#2859 Increment F+): par_reduces_p_spine_cong_below_boundary.
// The boundary-guarded spine congruence — a strict-partial (below-boundary)
// const-app spine par-reduces only by a pointwise spine congruence, because
// it can NEVER fire a top-level iota (the redex-creation case the c not-redex
// guard could not discharge, design §11/§13). A single par_reduces_p.rec with
// a CPS-PRODUCT motive carrying the three preserved facts so the iota_p arm's
// IH delivers head(e2)=nm + Le (len e2) K to iota_step_below_boundary_absurd.
// =====================================================================

/// `major_idx(meta)` — the recursor's iota boundary.
fn spine_below_major_idx() -> String {
    "(Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))".to_string()
}

/// Type of `par_reduces_p_spine_cong_below_boundary`.
fn par_reduces_p_spine_cong_below_boundary_type() -> String {
    let k = spine_below_major_idx();
    format!(
        "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name) (meta : RecMeta), \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> \
         Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta) -> \
         Le (list_length (kapp_args f)) {k} -> \
         par_reduces_p env f f' -> \
         par_reduces_p_list env (kapp_args f) (kapp_args f')"
    )
}

/// Type of `par_reduces_p_preserves_head_const_below_boundary` — the head-side
/// companion of the spine congruence (same guards, but the conclusion is head-const
/// preservation `head f' = some nm` rather than the spine congruence).
fn par_reduces_p_preserves_head_const_below_boundary_type() -> String {
    let k = spine_below_major_idx();
    format!(
        "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name) (meta : RecMeta), \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> \
         Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta) -> \
         Le (list_length (kapp_args f)) {k} -> \
         par_reduces_p env f f' -> \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn f')) (OptionType.some Name nm)"
    )
}

/// The shared `par_reduces_p.rec` application producing the final `AndType` product
/// `AndType (par_reduces_p_list (kapp_args f)(kapp_args f')) (HeadConstBox (head f') nm)`
/// for a below-boundary const-headed `f ⇒_p f'`. A single `par_reduces_p.rec` carrying
/// an `AndType`-PRODUCT motive that bundles the two preserved facts (the Type-valued
/// spine congruence `kapp_args s ⇒_p_list kapp_args t` + the head-const preservation
/// `head(t) = some nm`). The length boundedness `Le (len t) K` is DERIVED from the spine
/// congruence (length-eq) + the guard, so it need not be bundled — keeping the motive at
/// Sort 1. The iota_p arm discharges the fired iota via `iota_step_below_boundary_absurd`:
/// its IH on the sub-reduction `e0 ⇒_p e2` supplies head(e2)=nm + the spine-cong (hence
/// Le (len e2) K), exactly the below-boundary hypotheses the absurdity needs. Returns the
/// recursor application as a string over the binders `env f f' nm meta` and hypotheses
/// `h : par_reduces_p env f f'`, `hhead`, `hbelow` — shared by
/// `par_reduces_p_spine_cong_below_boundary_proof` (projects the spine) and
/// `par_reduces_p_preserves_head_const_below_boundary_proof` (projects + unboxes the head).
fn par_reduces_p_spine_cong_below_boundary_andtype() -> String {
    let k = spine_below_major_idx();
    // head x := kexpr_const_name (kapp_fn x); len x := list_length (kapp_args x).
    let head = |x: &str| format!("(kexpr_const_name (kapp_fn {x}))");
    let len = |x: &str| format!("(list_length (kapp_args {x}))");
    let some_nm = "(OptionType.some Name nm)";
    let plist =
        |s: &str, t: &str| format!("(par_reduces_p_list env (kapp_args {s}) (kapp_args {t}))");
    // The Prop eq type head(t) = some nm (unboxed).
    let head_eq_ty = |t: &str| format!("(Eq (OptionType Name) {} {some_nm})", head(t));
    // The Type-valued head-preservation fact: HeadConstBox (head t) nm (the boxed
    // Prop eq head(t) = some nm), so AndType (Type × Type) can carry it.
    let head_box = |t: &str| format!("(HeadConstBox {} nm)", head(t));
    // Construct the box from a Prop eq term `eq : head(t) = some nm`.
    let head_box_mk = |t: &str, eq: &str| format!("(HeadConstBox.mk {} nm {eq})", head(t));
    // Unbox: HeadConstBox.rec to deliver the Prop eq into a continuation `kont`
    // (a function of the eq) producing goal `goal`.
    let head_box_elim = |t: &str, box_term: &str, goal: &str, kont: &str| {
        format!(
            "(HeadConstBox.rec {ht} nm (fun (_b : {hb}) => {goal}) {kont} {box_term})",
            ht = head(t),
            hb = head_box(t),
        )
    };

    // The AndType product the motive delivers for a given (s, t): the spine
    // congruence AND the (boxed) head-const preservation.
    let product = |s: &str, t: &str| -> String {
        format!("(AndType {sp} {he})", sp = plist(s, t), he = head_box(t))
    };

    // Motive M s t _h := head(s) = some nm -> Le (len s) K -> product(s, t).
    // (product(s, t) bundles the spine congruence kapp_args s ⇒_p_list kapp_args t
    // and head(t) = some nm; the recursor instantiates t per ctor.)
    let motive = format!(
        "(fun (s : KExpr) (t : KExpr) (_h : par_reduces_p env s t) => \
         Eq (OptionType Name) {hs} {some_nm} -> Le {ls} {k} -> {prod})",
        hs = head("s"),
        ls = len("s"),
        prod = product("s", "t"),
    );

    // Discharge a binder-headed source SRC (head(SRC) = none by refl) against the
    // guard ghead : head(SRC) = some nm — produces the product for any reduct via
    // option_none_ne_some_type into Empty.
    let binder_discharge = |src: &str, red: &str, ghead: &str| -> String {
        format!(
            "(option_none_ne_some_type Name nm {prod} \
             (Eq.trans (OptionType Name) (OptionType.none Name) {hsrc} {some_nm} \
             (Eq.refl (OptionType Name) (OptionType.none Name)) {ghead}))",
            prod = product(src, red),
            hsrc = head(src),
            ghead = ghead,
        )
    };

    // refl arm: s -> s. AndType.intro (refl spine) (the boxed guard head-eq).
    let refl_arm = format!(
        "(fun (s : KExpr) (ghead : Eq (OptionType Name) {hs} {some_nm}) (_glen : Le {ls} {k}) => \
         AndType.intro {sp} {he} (par_reduces_p_list_refl env (kapp_args s)) {box})",
        hs = head("s"),
        ls = len("s"),
        box = head_box_mk("s", "ghead"),
        sp = plist("s", "s"),
        he = head_box("s"),
    );

    // app arm: s = app g0 b -> t = app g0' b'. IH(g0) gives product(g0, g0'); unbundle
    // it (AndType.rec) into spine_g0 + head_g0', derive len facts, build product(app..).
    let app_arm = {
        // head g0 = some nm: from ghead via kapp_fn_app.
        let head_g0 = format!(
            "(Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) {some_nm}) \
             (kapp_fn (KExpr.app g0 b)) (kapp_fn g0) (kapp_fn_app g0 b) ghead)"
        );
        // len_app_eq2_g : len (app g0 b) = succ (len g0).
        let len_app_eq2 = |g: &str, bb: &str| {
            format!(
            "(Eq.trans Nat {l_appgb} (list_length (list_append (kapp_args {g}) (ListType.cons KExpr {bb} (ListType.nil KExpr)))) (Nat.succ {l_g}) \
             (Eq.cong (ListType KExpr) Nat (fun (L : ListType KExpr) => list_length L) (kapp_args (KExpr.app {g} {bb})) (list_append (kapp_args {g}) (ListType.cons KExpr {bb} (ListType.nil KExpr))) (kapp_args_app {g} {bb})) \
             (list_length_append_singleton (kapp_args {g}) {bb}))",
            l_appgb = len(&format!("(KExpr.app {g} {bb})")),
            l_g = len(g),
        )
        };
        // glen : Le (len (app g0 b)) K -> Le (succ (len g0)) K -> Le (len g0) K (drop succ).
        let glen_succ_g0 = format!(
            "(Eq.subst Nat (fun (N : Nat) => Le N {k}) {l_appgb} (Nat.succ {l_g0}) {leq} glen)",
            l_appgb = len("(KExpr.app g0 b)"),
            l_g0 = len("g0"),
            leq = len_app_eq2("g0", "b"),
        );
        let glen_g0 = format!(
            "(le_trans {l_g0} (Nat.succ {l_g0}) {k} (Le.step {l_g0} {l_g0} (Le.refl {l_g0})) {glen_succ_g0})",
            l_g0 = len("g0"),
        );
        // Build product(app g0 b, app g0' b') by unbundling IH(g0).
        // Inside: spine_g0 : plist g0 g0'; head_g0' : head g0' = some nm.
        // head(app g0' b') = head g0' = some nm — built from the UNBOXED head_g0'eq.
        let head_appgpbp_eq = format!(
            "(Eq.trans (OptionType Name) {h_appgpbp} {h_g0p} {some_nm} \
             (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn (KExpr.app g0' b')) (kapp_fn g0') (kapp_fn_app g0' b')) \
             head_g0'eq)",
            h_appgpbp = head("(KExpr.app g0' b')"),
            h_g0p = head("g0'"),
        );
        // spine(app g0 b, app g0' b') = kapp_args_par_p on spine_g0 + hb.
        let spine_appgpbp = "(kapp_args_par_p env g0 g0' b b' spine_g0 hb)".to_string();
        let inner_intro = format!(
            "(AndType.intro {sp} {he} {spine_appgpbp} {box})",
            sp = plist("(KExpr.app g0 b)", "(KExpr.app g0' b')"),
            he = head_box("(KExpr.app g0' b')"),
            box = head_box_mk("(KExpr.app g0' b')", &head_appgpbp_eq),
        );
        // Unbox head_g0'_box -> head_g0'eq (the Prop eq) before building inner_intro.
        let inner_with_unbox = head_box_elim(
            "g0'",
            "head_g0'box",
            &product("(KExpr.app g0 b)", "(KExpr.app g0' b')"),
            &format!(
                "(fun (head_g0'eq : {}) => {inner_intro})",
                head_eq_ty("g0'")
            ),
        );
        // AndType.rec unbundling IH(g0) -> product(app..).
        let unbundle = format!(
            "(AndType.rec {sp_g0} {he_g0} (fun (_ab : AndType {sp_g0} {he_g0}) => {prod_app}) \
             (fun (spine_g0 : {sp_g0}) (head_g0'box : {he_g0}) => {inner_with_unbox}) \
             (ihg0 {head_g0} {glen_g0}))",
            sp_g0 = plist("g0", "g0'"),
            he_g0 = head_box("g0'"),
            prod_app = product("(KExpr.app g0 b)", "(KExpr.app g0' b')"),
            head_g0 = head_g0,
            glen_g0 = glen_g0,
            inner_with_unbox = inner_with_unbox,
        );
        format!(
            "(fun (g0 : KExpr) (g0' : KExpr) (b : KExpr) (b' : KExpr) \
             (hg : par_reduces_p env g0 g0') (hb : par_reduces_p env b b') \
             (ihg0 : Eq (OptionType Name) {h_g0} {some_nm} -> Le {l_g0} {k} -> {prod_g0}) \
             (_ihb : Eq (OptionType Name) {h_b} {some_nm} -> Le {l_b} {k} -> {prod_b}) \
             (ghead : Eq (OptionType Name) {h_appgb} {some_nm}) (glen : Le {l_appgb} {k}) => \
             {unbundle})",
            h_g0 = head("g0"),
            l_g0 = len("g0"),
            prod_g0 = product("g0", "g0'"),
            h_b = head("b"),
            l_b = len("b"),
            prod_b = product("b", "b'"),
            h_appgb = head("(KExpr.app g0 b)"),
            l_appgb = len("(KExpr.app g0 b)"),
            unbundle = unbundle,
        )
    };

    // binder/beta/let arms (head mismatch discharge).
    let beta_arm = format!(
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) \
         (_hA : par_reduces_p env A A') (_hbody : par_reduces_p env body body') (_harg : par_reduces_p env arg arg') \
         (_ihA : Eq (OptionType Name) {hA} {some_nm} -> Le {lA} {k} -> {prodA}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> Le {lbody} {k} -> {prodbody}) \
         (_iharg : Eq (OptionType Name) {harg} {some_nm} -> Le {larg} {k} -> {prodarg}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) (_glen : Le {lsrc} {k}) => \
         {discharge})",
        hA = head("A"), lA = len("A"), prodA = product("A", "A'"),
        hbody = head("body"), lbody = len("body"), prodbody = product("body", "body'"),
        harg = head("arg"), larg = len("arg"), prodarg = product("arg", "arg'"),
        hsrc = head("(KExpr.app (KExpr.lam A body) arg)"),
        lsrc = len("(KExpr.app (KExpr.lam A body) arg)"),
        discharge = binder_discharge("(KExpr.app (KExpr.lam A body) arg)", "(instantiate body' arg')", "ghead"),
    );
    let lam_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hty : par_reduces_p env ty ty') (_hbody : par_reduces_p env body body') \
         (_ihty : Eq (OptionType Name) {hty} {some_nm} -> Le {lty} {k} -> {prodty}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> Le {lbody} {k} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) (_glen : Le {lsrc} {k}) => \
         {discharge})",
        hty = head("ty"),
        lty = len("ty"),
        prodty = product("ty", "ty'"),
        hbody = head("body"),
        lbody = len("body"),
        prodbody = product("body", "body'"),
        hsrc = head("(KExpr.lam ty body)"),
        lsrc = len("(KExpr.lam ty body)"),
        discharge = binder_discharge("(KExpr.lam ty body)", "(KExpr.lam ty' body')", "ghead"),
    );
    let pi_arm = format!(
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hd : par_reduces_p env dom dom') (_hbody : par_reduces_p env body body') \
         (_ihd : Eq (OptionType Name) {hd} {some_nm} -> Le {ld} {k} -> {prodd}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> Le {lbody} {k} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) (_glen : Le {lsrc} {k}) => \
         {discharge})",
        hd = head("dom"),
        ld = len("dom"),
        prodd = product("dom", "dom'"),
        hbody = head("body"),
        lbody = len("body"),
        prodbody = product("body", "body'"),
        hsrc = head("(KExpr.pi dom body)"),
        lsrc = len("(KExpr.pi dom body)"),
        discharge = binder_discharge("(KExpr.pi dom body)", "(KExpr.pi dom' body')", "ghead"),
    );
    let forall_arm = format!(
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hd : par_reduces_p env dom dom') (_hbody : par_reduces_p env body body') \
         (_ihd : Eq (OptionType Name) {hd} {some_nm} -> Le {ld} {k} -> {prodd}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> Le {lbody} {k} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) (_glen : Le {lsrc} {k}) => \
         {discharge})",
        hd = head("dom"),
        ld = len("dom"),
        prodd = product("dom", "dom'"),
        hbody = head("body"),
        lbody = len("body"),
        prodbody = product("body", "body'"),
        hsrc = head("(KExpr.forall_ dom body)"),
        lsrc = len("(KExpr.forall_ dom body)"),
        discharge = binder_discharge(
            "(KExpr.forall_ dom body)",
            "(KExpr.forall_ dom' body')",
            "ghead"
        ),
    );
    let let_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') (_hbody : par_reduces_p env body body') \
         (_ihty : Eq (OptionType Name) {hty} {some_nm} -> Le {lty} {k} -> {prodty}) \
         (_ihval : Eq (OptionType Name) {hval} {some_nm} -> Le {lval} {k} -> {prodval}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> Le {lbody} {k} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) (_glen : Le {lsrc} {k}) => \
         {discharge})",
        hty = head("ty"), lty = len("ty"), prodty = product("ty", "ty'"),
        hval = head("val"), lval = len("val"), prodval = product("val", "val'"),
        hbody = head("body"), lbody = len("body"), prodbody = product("body", "body'"),
        hsrc = head("(KExpr.let_ ty val body)"), lsrc = len("(KExpr.let_ ty val body)"),
        discharge = binder_discharge("(KExpr.let_ ty val body)", "(instantiate body' val')", "ghead"),
    );
    // let_cong (trailing congruence): a let is its own spine head (head = none), so the
    // const-headed guard refutes exactly as the zeta arm — reduct KExpr.let_ ty' val' body'.
    let let_cong_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') (_hbody : par_reduces_p env body body') \
         (_ihty : Eq (OptionType Name) {hty} {some_nm} -> Le {lty} {k} -> {prodty}) \
         (_ihval : Eq (OptionType Name) {hval} {some_nm} -> Le {lval} {k} -> {prodval}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> Le {lbody} {k} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) (_glen : Le {lsrc} {k}) => \
         {discharge})",
        hty = head("ty"), lty = len("ty"), prodty = product("ty", "ty'"),
        hval = head("val"), lval = len("val"), prodval = product("val", "val'"),
        hbody = head("body"), lbody = len("body"), prodbody = product("body", "body'"),
        hsrc = head("(KExpr.let_ ty val body)"), lsrc = len("(KExpr.let_ ty val body)"),
        discharge = binder_discharge("(KExpr.let_ ty val body)", "(KExpr.let_ ty' val' body')", "ghead"),
    );

    // proj arm: source proj s i sub is its own spine head (head = none), so the
    // some-nm guard refutes it — same binder_discharge as the lam/let arms.
    let proj_arm = format!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) \
         (_hsub : par_reduces_p env sub sub') \
         (_ihsub : Eq (OptionType Name) {hsub} {some_nm} -> Le {lsub} {k} -> {prodsub}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) (_glen : Le {lsrc} {k}) => \
         {discharge})",
        hsub = head("sub"),
        lsub = len("sub"),
        prodsub = product("sub", "sub'"),
        hsrc = head("(KExpr.proj s i sub)"),
        lsrc = len("(KExpr.proj s i sub)"),
        discharge = binder_discharge("(KExpr.proj s i sub)", "(KExpr.proj s i sub')", "ghead"),
    );

    // iota_p arm: e0 ⇒_p e2, iota_step e2 r0. The wall: unbundle IH(e0⇒e2) into
    // spine_e2 + head_e2; derive Le (len e2) K from spine_e2 (length-eq) + the guard;
    // iota_step_below_boundary_absurd refutes the fire on e2.
    let iota_arm = {
        // Le (len e2) K from spine_e2 + glen(e0): len e0 = len e2, glen : Le (len e0) K.
        let len_eq = "(par_reduces_p_list_length_eq env (kapp_args e0) (kapp_args e2) spine_e2)";
        let le_e2 = format!(
            "(Eq.subst Nat (fun (N : Nat) => Le N {k}) {l_e0} {l_e2} {len_eq} glen)",
            l_e0 = len("e0"),
            l_e2 = len("e2"),
        );
        // Unbox head_e2box -> head_e2 (Prop eq), then feed the absurd brick.
        let absurd_with_unbox = head_box_elim(
            "e2",
            "head_e2box",
            &product("e0", "r0"),
            &format!(
                "(fun (head_e2 : {het}) => \
                 iota_step_below_boundary_absurd env e2 r0 nm meta {prod_e0r0} head_e2 hmeta {le_e2} hi0)",
                het = head_eq_ty("e2"),
                prod_e0r0 = product("e0", "r0"),
                le_e2 = le_e2,
            ),
        );
        let unbundle = format!(
            "(AndType.rec {sp_e0e2} {he_e2} (fun (_ab : AndType {sp_e0e2} {he_e2}) => {prod_e0r0}) \
             (fun (spine_e2 : {sp_e0e2}) (head_e2box : {he_e2}) => {absurd_with_unbox}) \
             (ihprem ghead glen))",
            sp_e0e2 = plist("e0", "e2"),
            he_e2 = head_box("e2"),
            prod_e0r0 = product("e0", "r0"),
            absurd_with_unbox = absurd_with_unbox,
        );
        format!(
            "(fun (e0 : KExpr) (e2 : KExpr) (r0 : KExpr) \
             (hprem : par_reduces_p env e0 e2) (hi0 : iota_step env e2 r0) \
             (ihprem : Eq (OptionType Name) {h_e0} {some_nm} -> Le {l_e0} {k} -> {prod_e0e2}) \
             (ghead : Eq (OptionType Name) {h_e0g} {some_nm}) (glen : Le {l_e0g} {k}) => \
             {unbundle})",
            h_e0 = head("e0"),
            l_e0 = len("e0"),
            prod_e0e2 = product("e0", "e2"),
            h_e0g = head("e0"),
            l_e0g = len("e0"),
            unbundle = unbundle,
        )
    };

    // The recursor application producing the final AndType product
    // AndType (plist f f') (head_box f') — shared between the spine-cong lemma (which
    // projects the spine) and par_reduces_p_preserves_head_const_below_boundary
    // (which projects + unboxes the head).
    format!(
        "(par_reduces_p.rec env {motive} \
         {refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} \
         f f' h hhead hbelow)"
    )
}

/// Closed proof term for `par_reduces_p_spine_cong_below_boundary`. Runs the shared
/// `par_reduces_p_spine_cong_below_boundary_andtype` recursor, then projects the SPINE
/// congruence out of the final product via `AndType.rec`.
fn par_reduces_p_spine_cong_below_boundary_proof() -> String {
    let k = spine_below_major_idx();
    let head = |x: &str| format!("(kexpr_const_name (kapp_fn {x}))");
    let len = |x: &str| format!("(list_length (kapp_args {x}))");
    let some_nm = "(OptionType.some Name nm)";
    let plist =
        |s: &str, t: &str| format!("(par_reduces_p_list env (kapp_args {s}) (kapp_args {t}))");
    let head_box = |t: &str| format!("(HeadConstBox {} nm)", head(t));

    let recursor_andtype = par_reduces_p_spine_cong_below_boundary_andtype();

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name) (meta : RecMeta) \
         (hhead : Eq (OptionType Name) {hf} {some_nm}) \
         (hmeta : Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta)) \
         (hbelow : Le {lf} {k}) \
         (h : par_reduces_p env f f') => \
         AndType.rec {sp_ff} {he_f} (fun (_ab : AndType {sp_ff} {he_f}) => {sp_ff}) \
         (fun (spine : {sp_ff}) (_he : {he_f}) => spine) \
         {recursor_andtype}",
        hf = head("f"),
        lf = len("f"),
        sp_ff = plist("f", "f'"),
        he_f = head_box("f'"),
    )
}

/// Closed proof term for `par_reduces_p_preserves_head_const_below_boundary`. Reuses
/// the EXACT AndType-product recursor of `par_reduces_p_spine_cong_below_boundary_proof`
/// (identical motive + all 9 arms incl. the trailing let_cong — the iota_p arm discharged by
/// `iota_step_below_boundary_absurd`), but projects + UNBOXES the head-const half of the
/// final product instead of the spine half. So under the below-boundary recursor guard,
/// a const-headed `f ⇒_p f'` preserves the head const: `head f' = some nm`. The
/// head-side companion of the spine congruence (the p-side analogue of the c-side
/// `par_reduces_c_preserves_head_const_nr`, whose not-redex guard does NOT port — here
/// the below-boundary arithmetic guard does the discharging instead, design §11).
fn par_reduces_p_preserves_head_const_below_boundary_proof() -> String {
    let k = spine_below_major_idx();
    let head = |x: &str| format!("(kexpr_const_name (kapp_fn {x}))");
    let len = |x: &str| format!("(list_length (kapp_args {x}))");
    let some_nm = "(OptionType.some Name nm)";
    let plist =
        |s: &str, t: &str| format!("(par_reduces_p_list env (kapp_args {s}) (kapp_args {t}))");
    let head_eq_ty = |t: &str| format!("(Eq (OptionType Name) {} {some_nm})", head(t));
    let head_box = |t: &str| format!("(HeadConstBox {} nm)", head(t));

    let recursor_andtype = par_reduces_p_spine_cong_below_boundary_andtype();

    // Project the head box out of the product (second component), then unbox it
    // (HeadConstBox.rec) to deliver the Prop eq head f' = some nm.
    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name) (meta : RecMeta) \
         (hhead : Eq (OptionType Name) {hf} {some_nm}) \
         (hmeta : Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta)) \
         (hbelow : Le {lf} {k}) \
         (h : par_reduces_p env f f') => \
         HeadConstBox.rec {hfp} nm (fun (_b : {he_f}) => {head_eq_fp}) \
         (fun (eqfp : {head_eq_fp}) => eqfp) \
         (AndType.rec {sp_ff} {he_f} (fun (_ab : AndType {sp_ff} {he_f}) => {he_f}) \
         (fun (_spine : {sp_ff}) (hebox : {he_f}) => hebox) \
         {recursor_andtype})",
        hf = head("f"),
        hfp = head("f'"),
        lf = len("f"),
        sp_ff = plist("f", "f'"),
        he_f = head_box("f'"),
        head_eq_fp = head_eq_ty("f'"),
    )
}

// =====================================================================
// par_reduces_p_spine_cong_no_recmeta — the constructor-headed-major companion
// of the below-boundary spine congruence. Same AndType-product recursion, but
// the guard is the no-recmeta faithful hypothesis (recmeta_for env nm = none)
// and the iota_p arm discharges via iota_step_no_recmeta_absurd (no arithmetic).
// =====================================================================

/// Type of `par_reduces_p_spine_cong_no_recmeta`.
fn par_reduces_p_spine_cong_no_recmeta_type() -> String {
    "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name), \
     Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> \
     Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.none RecMeta) -> \
     par_reduces_p env f f' -> \
     par_reduces_p_list env (kapp_args f) (kapp_args f')"
        .to_string()
}

/// The shared `par_reduces_p.rec` application producing the final `AndType` product
/// `AndType (par_reduces_p_list (kapp_args f)(kapp_args f')) (HeadConstBox (head f') nm)`
/// for a no-recmeta const-headed `f ⇒_p f'`. Mirror of
/// `par_reduces_p_spine_cong_below_boundary_andtype` with the Le guard dropped from the
/// motive/arms and the iota_p arm discharged via `iota_step_no_recmeta_absurd`. Returns
/// the recursor application over the binders `env f f' nm` and hypotheses
/// `h : par_reduces_p env f f'`, `hhead`, `hnone` — shared by
/// `par_reduces_p_spine_cong_no_recmeta_proof` (projects the spine) and
/// `par_reduces_p_preserves_head_const_no_recmeta_proof` (projects + unboxes the head).
fn par_reduces_p_spine_cong_no_recmeta_andtype() -> String {
    let head = |x: &str| format!("(kexpr_const_name (kapp_fn {x}))");
    let some_nm = "(OptionType.some Name nm)";
    let plist =
        |s: &str, t: &str| format!("(par_reduces_p_list env (kapp_args {s}) (kapp_args {t}))");
    let head_eq_ty = |t: &str| format!("(Eq (OptionType Name) {} {some_nm})", head(t));
    let head_box = |t: &str| format!("(HeadConstBox {} nm)", head(t));
    let head_box_mk = |t: &str, eq: &str| format!("(HeadConstBox.mk {} nm {eq})", head(t));
    let head_box_elim = |t: &str, box_term: &str, goal: &str, kont: &str| {
        format!(
            "(HeadConstBox.rec {ht} nm (fun (_b : {hb}) => {goal}) {kont} {box_term})",
            ht = head(t),
            hb = head_box(t),
        )
    };
    let product = |s: &str, t: &str| -> String {
        format!("(AndType {sp} {he})", sp = plist(s, t), he = head_box(t))
    };

    // Motive M s t _h := head(s) = some nm -> product(s, t). (No Le guard.)
    let motive = format!(
        "(fun (s : KExpr) (t : KExpr) (_h : par_reduces_p env s t) => \
         Eq (OptionType Name) {hs} {some_nm} -> {prod})",
        hs = head("s"),
        prod = product("s", "t"),
    );

    let binder_discharge = |src: &str, red: &str, ghead: &str| -> String {
        format!(
            "(option_none_ne_some_type Name nm {prod} \
             (Eq.trans (OptionType Name) (OptionType.none Name) {hsrc} {some_nm} \
             (Eq.refl (OptionType Name) (OptionType.none Name)) {ghead}))",
            prod = product(src, red),
            hsrc = head(src),
            ghead = ghead,
        )
    };

    // refl arm: AndType.intro (refl spine) (boxed guard head-eq).
    let refl_arm = format!(
        "(fun (s : KExpr) (ghead : Eq (OptionType Name) {hs} {some_nm}) => \
         AndType.intro {sp} {he} (par_reduces_p_list_refl env (kapp_args s)) {box})",
        hs = head("s"),
        box = head_box_mk("s", "ghead"),
        sp = plist("s", "s"),
        he = head_box("s"),
    );

    // app arm: s = app g0 b -> t = app g0' b'. IH(g0) gives product(g0, g0').
    let app_arm = {
        let head_g0 = format!(
            "(Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) {some_nm}) \
             (kapp_fn (KExpr.app g0 b)) (kapp_fn g0) (kapp_fn_app g0 b) ghead)"
        );
        let head_appgpbp_eq = format!(
            "(Eq.trans (OptionType Name) {h_appgpbp} {h_g0p} {some_nm} \
             (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn (KExpr.app g0' b')) (kapp_fn g0') (kapp_fn_app g0' b')) \
             head_g0'eq)",
            h_appgpbp = head("(KExpr.app g0' b')"),
            h_g0p = head("g0'"),
        );
        let spine_appgpbp = "(kapp_args_par_p env g0 g0' b b' spine_g0 hb)".to_string();
        let inner_intro = format!(
            "(AndType.intro {sp} {he} {spine_appgpbp} {box})",
            sp = plist("(KExpr.app g0 b)", "(KExpr.app g0' b')"),
            he = head_box("(KExpr.app g0' b')"),
            box = head_box_mk("(KExpr.app g0' b')", &head_appgpbp_eq),
        );
        let inner_with_unbox = head_box_elim(
            "g0'",
            "head_g0'box",
            &product("(KExpr.app g0 b)", "(KExpr.app g0' b')"),
            &format!(
                "(fun (head_g0'eq : {}) => {inner_intro})",
                head_eq_ty("g0'")
            ),
        );
        let unbundle = format!(
            "(AndType.rec {sp_g0} {he_g0} (fun (_ab : AndType {sp_g0} {he_g0}) => {prod_app}) \
             (fun (spine_g0 : {sp_g0}) (head_g0'box : {he_g0}) => {inner_with_unbox}) \
             (ihg0 {head_g0}))",
            sp_g0 = plist("g0", "g0'"),
            he_g0 = head_box("g0'"),
            prod_app = product("(KExpr.app g0 b)", "(KExpr.app g0' b')"),
            head_g0 = head_g0,
            inner_with_unbox = inner_with_unbox,
        );
        format!(
            "(fun (g0 : KExpr) (g0' : KExpr) (b : KExpr) (b' : KExpr) \
             (hg : par_reduces_p env g0 g0') (hb : par_reduces_p env b b') \
             (ihg0 : Eq (OptionType Name) {h_g0} {some_nm} -> {prod_g0}) \
             (_ihb : Eq (OptionType Name) {h_b} {some_nm} -> {prod_b}) \
             (ghead : Eq (OptionType Name) {h_appgb} {some_nm}) => \
             {unbundle})",
            h_g0 = head("g0"),
            prod_g0 = product("g0", "g0'"),
            h_b = head("b"),
            prod_b = product("b", "b'"),
            h_appgb = head("(KExpr.app g0 b)"),
            unbundle = unbundle,
        )
    };

    let beta_arm = format!(
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) \
         (_hA : par_reduces_p env A A') (_hbody : par_reduces_p env body body') (_harg : par_reduces_p env arg arg') \
         (_ihA : Eq (OptionType Name) {hA} {some_nm} -> {prodA}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> {prodbody}) \
         (_iharg : Eq (OptionType Name) {harg} {some_nm} -> {prodarg}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) => {discharge})",
        hA = head("A"), prodA = product("A", "A'"),
        hbody = head("body"), prodbody = product("body", "body'"),
        harg = head("arg"), prodarg = product("arg", "arg'"),
        hsrc = head("(KExpr.app (KExpr.lam A body) arg)"),
        discharge = binder_discharge("(KExpr.app (KExpr.lam A body) arg)", "(instantiate body' arg')", "ghead"),
    );
    let lam_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hty : par_reduces_p env ty ty') (_hbody : par_reduces_p env body body') \
         (_ihty : Eq (OptionType Name) {hty} {some_nm} -> {prodty}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) => {discharge})",
        hty = head("ty"),
        prodty = product("ty", "ty'"),
        hbody = head("body"),
        prodbody = product("body", "body'"),
        hsrc = head("(KExpr.lam ty body)"),
        discharge = binder_discharge("(KExpr.lam ty body)", "(KExpr.lam ty' body')", "ghead"),
    );
    let pi_arm = format!(
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hd : par_reduces_p env dom dom') (_hbody : par_reduces_p env body body') \
         (_ihd : Eq (OptionType Name) {hd} {some_nm} -> {prodd}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) => {discharge})",
        hd = head("dom"),
        prodd = product("dom", "dom'"),
        hbody = head("body"),
        prodbody = product("body", "body'"),
        hsrc = head("(KExpr.pi dom body)"),
        discharge = binder_discharge("(KExpr.pi dom body)", "(KExpr.pi dom' body')", "ghead"),
    );
    let forall_arm = format!(
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hd : par_reduces_p env dom dom') (_hbody : par_reduces_p env body body') \
         (_ihd : Eq (OptionType Name) {hd} {some_nm} -> {prodd}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) => {discharge})",
        hd = head("dom"),
        prodd = product("dom", "dom'"),
        hbody = head("body"),
        prodbody = product("body", "body'"),
        hsrc = head("(KExpr.forall_ dom body)"),
        discharge = binder_discharge(
            "(KExpr.forall_ dom body)",
            "(KExpr.forall_ dom' body')",
            "ghead"
        ),
    );
    let let_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') (_hbody : par_reduces_p env body body') \
         (_ihty : Eq (OptionType Name) {hty} {some_nm} -> {prodty}) \
         (_ihval : Eq (OptionType Name) {hval} {some_nm} -> {prodval}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) => {discharge})",
        hty = head("ty"), prodty = product("ty", "ty'"),
        hval = head("val"), prodval = product("val", "val'"),
        hbody = head("body"), prodbody = product("body", "body'"),
        hsrc = head("(KExpr.let_ ty val body)"),
        discharge = binder_discharge("(KExpr.let_ ty val body)", "(instantiate body' val')", "ghead"),
    );
    // let_cong (trailing congruence): a let is its own spine head (head = none), so the
    // const-headed guard refutes exactly as the zeta arm — reduct KExpr.let_ ty' val' body'.
    let let_cong_arm = format!(
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) \
         (_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') (_hbody : par_reduces_p env body body') \
         (_ihty : Eq (OptionType Name) {hty} {some_nm} -> {prodty}) \
         (_ihval : Eq (OptionType Name) {hval} {some_nm} -> {prodval}) \
         (_ihbody : Eq (OptionType Name) {hbody} {some_nm} -> {prodbody}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) => {discharge})",
        hty = head("ty"), prodty = product("ty", "ty'"),
        hval = head("val"), prodval = product("val", "val'"),
        hbody = head("body"), prodbody = product("body", "body'"),
        hsrc = head("(KExpr.let_ ty val body)"),
        discharge = binder_discharge("(KExpr.let_ ty val body)", "(KExpr.let_ ty' val' body')", "ghead"),
    );

    // proj arm: proj is its own spine head (head = none) — the some-nm guard refutes it.
    let proj_arm = format!(
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) \
         (_hsub : par_reduces_p env sub sub') \
         (_ihsub : Eq (OptionType Name) {hsub} {some_nm} -> {prodsub}) \
         (ghead : Eq (OptionType Name) {hsrc} {some_nm}) => {discharge})",
        hsub = head("sub"),
        prodsub = product("sub", "sub'"),
        hsrc = head("(KExpr.proj s i sub)"),
        discharge = binder_discharge("(KExpr.proj s i sub)", "(KExpr.proj s i sub')", "ghead"),
    );

    // iota_p arm: discharge via iota_step_no_recmeta_absurd (head(e2)=nm from IH +
    // hnone) — no length needed.
    let iota_arm = {
        let absurd_with_unbox = head_box_elim(
            "e2",
            "head_e2box",
            &product("e0", "r0"),
            &format!(
                "(fun (head_e2 : {het}) => \
                 iota_step_no_recmeta_absurd env e2 r0 nm {prod_e0r0} head_e2 hnone hi0)",
                het = head_eq_ty("e2"),
                prod_e0r0 = product("e0", "r0"),
            ),
        );
        let unbundle = format!(
            "(AndType.rec {sp_e0e2} {he_e2} (fun (_ab : AndType {sp_e0e2} {he_e2}) => {prod_e0r0}) \
             (fun (spine_e2 : {sp_e0e2}) (head_e2box : {he_e2}) => {absurd_with_unbox}) \
             (ihprem ghead))",
            sp_e0e2 = plist("e0", "e2"),
            he_e2 = head_box("e2"),
            prod_e0r0 = product("e0", "r0"),
            absurd_with_unbox = absurd_with_unbox,
        );
        format!(
            "(fun (e0 : KExpr) (e2 : KExpr) (r0 : KExpr) \
             (hprem : par_reduces_p env e0 e2) (hi0 : iota_step env e2 r0) \
             (ihprem : Eq (OptionType Name) {h_e0} {some_nm} -> {prod_e0e2}) \
             (ghead : Eq (OptionType Name) {h_e0g} {some_nm}) => {unbundle})",
            h_e0 = head("e0"),
            prod_e0e2 = product("e0", "e2"),
            h_e0g = head("e0"),
            unbundle = unbundle,
        )
    };

    // The recursor application producing the final AndType product (no Le guard) —
    // shared between this spine-cong lemma and the head-side companion
    // par_reduces_p_preserves_head_const_no_recmeta.
    format!(
        "(par_reduces_p.rec env {motive} \
         {refl_arm} {beta_arm} {app_arm} {lam_arm} {pi_arm} {forall_arm} {let_arm} {iota_arm} {let_cong_arm} {proj_arm} \
         f f' h hhead)"
    )
}

/// Closed proof term for `par_reduces_p_spine_cong_no_recmeta`. Runs the shared
/// `par_reduces_p_spine_cong_no_recmeta_andtype` recursor, then projects the SPINE
/// congruence out of the final product via `AndType.rec`.
fn par_reduces_p_spine_cong_no_recmeta_proof() -> String {
    let head = |x: &str| format!("(kexpr_const_name (kapp_fn {x}))");
    let some_nm = "(OptionType.some Name nm)";
    let plist =
        |s: &str, t: &str| format!("(par_reduces_p_list env (kapp_args {s}) (kapp_args {t}))");
    let head_box = |t: &str| format!("(HeadConstBox {} nm)", head(t));

    let recursor_andtype = par_reduces_p_spine_cong_no_recmeta_andtype();

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name) \
         (hhead : Eq (OptionType Name) {hf} {some_nm}) \
         (hnone : Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.none RecMeta)) \
         (h : par_reduces_p env f f') => \
         AndType.rec {sp_ff} {he_f} (fun (_ab : AndType {sp_ff} {he_f}) => {sp_ff}) \
         (fun (spine : {sp_ff}) (_he : {he_f}) => spine) \
         {recursor_andtype}",
        hf = head("f"),
        sp_ff = plist("f", "f'"),
        he_f = head_box("f'"),
    )
}

/// Type of `par_reduces_p_preserves_head_const_no_recmeta` — the head-side companion
/// of the no-recmeta spine congruence (same guards, conclusion is head-const
/// preservation `head f' = some nm`).
fn par_reduces_p_preserves_head_const_no_recmeta_type() -> String {
    "forall (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name), \
     Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> \
     Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.none RecMeta) -> \
     par_reduces_p env f f' -> \
     Eq (OptionType Name) (kexpr_const_name (kapp_fn f')) (OptionType.some Name nm)"
        .to_string()
}

/// Closed proof term for `par_reduces_p_preserves_head_const_no_recmeta`. Reuses the
/// EXACT AndType-product recursor of `par_reduces_p_spine_cong_no_recmeta` (identical
/// motive + 9 arms (incl. the trailing let_cong) — the iota_p arm discharged by `iota_step_no_recmeta_absurd`), but
/// projects + UNBOXES the head-const half of the product instead of the spine half. So
/// under the no-recmeta constructor guard, a const-headed `f ⇒_p f'` preserves the head
/// const: `head f' = some nm`. The constructor-head companion of
/// `par_reduces_p_preserves_head_const_below_boundary`; consumed by the (iota,app)
/// minimal-join reduct reconstruction to lift the major's head const past `g ⇒_p g'`.
fn par_reduces_p_preserves_head_const_no_recmeta_proof() -> String {
    let head = |x: &str| format!("(kexpr_const_name (kapp_fn {x}))");
    let some_nm = "(OptionType.some Name nm)";
    let plist =
        |s: &str, t: &str| format!("(par_reduces_p_list env (kapp_args {s}) (kapp_args {t}))");
    let head_eq_ty = |t: &str| format!("(Eq (OptionType Name) {} {some_nm})", head(t));
    let head_box = |t: &str| format!("(HeadConstBox {} nm)", head(t));

    let recursor_andtype = par_reduces_p_spine_cong_no_recmeta_andtype();

    format!(
        "fun (env : RecEnv) (f : KExpr) (f' : KExpr) (nm : Name) \
         (hhead : Eq (OptionType Name) {hf} {some_nm}) \
         (hnone : Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.none RecMeta)) \
         (h : par_reduces_p env f f') => \
         HeadConstBox.rec {hfp} nm (fun (_b : {he_f}) => {head_eq_fp}) \
         (fun (eqfp : {head_eq_fp}) => eqfp) \
         (AndType.rec {sp_ff} {he_f} (fun (_ab : AndType {sp_ff} {he_f}) => {he_f}) \
         (fun (_spine : {sp_ff}) (hebox : {he_f}) => hebox) \
         {recursor_andtype})",
        hf = head("f"),
        hfp = head("f'"),
        sp_ff = plist("f", "f'"),
        he_f = head_box("f'"),
        head_eq_fp = head_eq_ty("f'"),
    )
}

// =====================================================================
// L2 brick (#2859 Increment F+): par_reduces_p_strict_partial_no_iota.
// A recursor application whose spine length EQUALS the major boundary
// does not fire a top-level iota (iota_reduct env f = none). Proved by
// an OptionType.rec convoy on iota_reduct env f: the some-arm is absurd
// via iota_reduct_some_inv + length-stability at the boundary.
// =====================================================================

/// Type of `par_reduces_p_strict_partial_no_iota`.
fn par_reduces_p_strict_partial_no_iota_type() -> String {
    let k = spine_below_major_idx();
    format!(
        "forall (env : RecEnv) (f : KExpr) (nm : Name) (meta : RecMeta), \
         Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> \
         Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta) -> \
         Eq Nat (list_length (kapp_args f)) {k} -> \
         Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)"
    )
}

/// Closed proof term for `par_reduces_p_strict_partial_no_iota`.
fn par_reduces_p_strict_partial_no_iota_proof() -> String {
    // major_idx over an arbitrary meta variable name.
    let major_idx_of = |m: &str| -> String {
        format!("(Nat.add (Nat.add (Nat.add (recmeta_num_params {m}) (recmeta_num_motives {m})) (recmeta_num_minors {m})) (recmeta_num_indices {m}))")
    };
    let k = major_idx_of("meta"); // the caller's boundary, == length (kapp_args f) by hlen.
    let k2 = major_idx_of("meta2"); // the inverted boundary, before pinning meta2 = meta.

    // The some-arm continuation: from heq : iota_reduct env f = some e', invert and
    // refute. Produces Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr).
    //
    // iota_reduct_some_inv env f e' GOAL heq (fun recname2 meta2 major2 cname2 rule2
    //   h1 h2 h3 h4 h5 h5r => REFUTE) where GOAL is the none-equation we want.
    //   h1 : kexpr_const_name (kapp_fn f) = some recname2
    //   h2 : recmeta_for env recname2 = some meta2
    //   h3 : list_head (list_drop K2 (kapp_args f)) = some major2
    //
    // STEP A: recname2 = nm.  hhead : ... = some nm; h1 : ... = some recname2.
    //   some nm = some recname2 (trans symm hhead, h1); option_some_inj -> nm = recname2.
    let nm_eq_recname2 = "(option_some_inj Name nm recname2 \
         (Eq.trans (OptionType Name) (OptionType.some Name nm) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname2) \
         (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) hhead) h1))";
    // STEP B: meta2 = meta.  h2 : recmeta_for env recname2 = some meta2.
    //   transport recname2 -> nm via (symm nm_eq_recname2): recmeta_for env nm = some meta2.
    //   hmeta : recmeta_for env nm = some meta. -> some meta = some meta2 -> meta = meta2.
    let h2_at_nm = format!(
        "(Eq.subst Name (fun (RN : Name) => Eq (OptionType RecMeta) (recmeta_for env RN) (OptionType.some RecMeta meta2)) \
         recname2 nm (Eq.symm Name nm recname2 {nm_eq_recname2}) h2)"
    );
    let meta_eq_meta2 = format!(
        "(option_some_inj RecMeta meta meta2 \
         (Eq.trans (OptionType RecMeta) (OptionType.some RecMeta meta) (recmeta_for env nm) (OptionType.some RecMeta meta2) \
         (Eq.symm (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta) hmeta) {h2_at_nm}))"
    );
    // STEP C: rewrite h3's index K2 -> K (= length (kapp_args f)).
    //   First meta2 -> meta in h3 (so K2 -> K): h3 : list_head (list_drop K2 (kapp_args f)) = some major2.
    let h3_at_meta = format!(
        "(Eq.subst RecMeta (fun (M : RecMeta) => Eq (OptionType KExpr) (list_head (list_drop {k2m} (kapp_args f))) (OptionType.some KExpr major2)) \
         meta2 meta (Eq.symm RecMeta meta meta2 {meta_eq_meta2}) h3)",
        k2m = major_idx_of("M"),
    );
    // Then K -> length (kapp_args f) via (symm hlen): h3 : list_head (list_drop length (kapp_args f)) = some major2.
    let h3_at_len = format!(
        "(Eq.subst Nat (fun (N : Nat) => Eq (OptionType KExpr) (list_head (list_drop N (kapp_args f))) (OptionType.some KExpr major2)) \
         {k} (list_length (kapp_args f)) (Eq.symm Nat (list_length (kapp_args f)) {k} hlen) \
         {h3_at_meta})"
    );
    // STEP D: list_head_drop_some_le_succ length (kapp_args f) major2 (h3_at_len)
    //   : Le (succ (length (kapp_args f))) (length (kapp_args f)).
    let le_self = format!(
        "(list_head_drop_some_le_succ (list_length (kapp_args f)) (kapp_args f) major2 {h3_at_len})"
    );
    // le_succ_self_empty (length (kapp_args f)) (le_self) : Empty; Empty.rec into the goal.
    let refute = format!(
        "(Empty.rec (fun (_e : Empty) => Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) \
         (le_succ_self_empty (list_length (kapp_args f)) {le_self}))"
    );

    // The some-arm of the OptionType convoy: given e' and heq : iota_reduct env f = some e',
    // derive the none-equation. (The convoy carries heq : iota_reduct env f = o.)
    let some_arm = format!(
        "(fun (e2 : KExpr) (heq : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.some KExpr e2)) => \
         iota_reduct_some_inv env f e2 (Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) heq \
         (fun (recname2 : Name) (meta2 : RecMeta) (major2 : KExpr) (cname2 : Name) (rule2 : RecRule) \
         (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname2)) \
         (h2 : Eq (OptionType RecMeta) (recmeta_for env recname2) (OptionType.some RecMeta meta2)) \
         (h3 : Eq (OptionType KExpr) (list_head (list_drop {k2} (kapp_args f))) (OptionType.some KExpr major2)) \
         (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn major2)) (OptionType.some Name cname2)) \
         (h5 : Eq (OptionType RecRule) (recrule_for env recname2 cname2) (OptionType.some RecRule rule2)) \
         (h5r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ {k2}) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule2)) (kapp_args major2)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta2) (recmeta_num_motives meta2)) (recmeta_num_minors meta2)) (kapp_args f)) (recrule_rhs rule2))))) (OptionType.some KExpr e2)) => \
         {refute}))"
    );
    // none-arm: o = none, heq : iota_reduct env f = none -> return heq.
    let none_arm =
        "(fun (heq : Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr)) => heq)";

    // Convoy motive over o : OptionType KExpr:
    //   fun o => Eq (OptionType KExpr) (iota_reduct env f) o -> (none-equation)
    let motive = "(fun (o : OptionType KExpr) => Eq (OptionType KExpr) (iota_reduct env f) o -> \
         Eq (OptionType KExpr) (iota_reduct env f) (OptionType.none KExpr))";

    format!(
        "fun (env : RecEnv) (f : KExpr) (nm : Name) (meta : RecMeta) \
         (hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm)) \
         (hmeta : Eq (OptionType RecMeta) (recmeta_for env nm) (OptionType.some RecMeta meta)) \
         (hlen : Eq Nat (list_length (kapp_args f)) {k}) => \
         OptionType.rec KExpr {motive} {none_arm} {some_arm} (iota_reduct env f) \
         (Eq.refl (OptionType KExpr) (iota_reduct env f))"
    )
}

/// Closed proof term for `par_reduces_p_preserves_head_const` — the c→p port of the
/// GENERIC const-head preservation (`par_reduces_c_preserves_head_const`,
/// par_reduces_c.rs:1157). A single `par_reduces_p.rec` over the step with the
/// guarded-Prop motive `M s t _ := head s = some nm -> C` (head x :=
/// `kexpr_const_name (kapp_fn x)`); refl returns the `ksurv` continuation; app lifts
/// the head via `Eq.subst` + `kapp_fn_app` into the head IH; the beta/binder/let arms
/// are discharged by the guard (their `kapp_fn` is a binder ⟹ `kexpr_const_name =
/// none`, contradicting `some nm` via `option_none_ne_some`); the iota_p arm forwards
/// its reduced-form fire `(e2, r, hi)` into the `kiota` continuation. Adapted verbatim
/// from the c-side body modulo `par_reduces_c → par_reduces_p` and the iota_p arm's
/// recursive-premise shape `(e, e2, r) (he) (hi) (ihe)`.
fn par_reduces_p_preserves_head_const_proof() -> String {
    concat!(
        "fun (env : RecEnv) (e : KExpr) (e' : KExpr) (nm : Name) (C : Prop) ",
        "(hhead : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm)) ",
        "(h : par_reduces_p env e e') ",
        "(ksurv : forall (t : KExpr), Eq (OptionType Name) (kexpr_const_name (kapp_fn t)) (OptionType.some Name nm) -> C) ",
        "(kiota : forall (t1 : KExpr) (t2 : KExpr), iota_step env t1 t2 -> C) => ",
        "par_reduces_p.rec env ",
        // motive: M e0 e0' _ := head e0 = some nm -> C
        "(fun (e0 : KExpr) (e0' : KExpr) (_h : par_reduces_p env e0 e0') => ",
        "Eq (OptionType Name) (kexpr_const_name (kapp_fn e0)) (OptionType.some Name nm) -> C) ",
        // refl arm
        "(fun (a : KExpr) (g : Eq (OptionType Name) (kexpr_const_name (kapp_fn a)) (OptionType.some Name nm)) => ksurv a g) ",
        // beta arm: e0 = app (lam A body) arg -> head = none, discharge
        "(fun (A : KExpr) (A' : KExpr) (body : KExpr) (body' : KExpr) (arg : KExpr) (arg' : KExpr) ",
        "(_hA : par_reduces_p env A A') (_hbody : par_reduces_p env body body') (_harg : par_reduces_p env arg arg') ",
        "(_ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> C) ",
        "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) ",
        "(_iharg : Eq (OptionType Name) (kexpr_const_name (kapp_fn arg)) (OptionType.some Name nm) -> C) ",
        "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (OptionType.some Name nm)) => ",
        "option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
        // app arm: e0 = app f a -> head (app f a) = head f, lift the guard via kapp_fn_app into the head IH
        "(fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) ",
        "(_hf : par_reduces_p env f f') (_ha : par_reduces_p env a a') ",
        "(ihf : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> C) ",
        "(_iha : Eq (OptionType Name) (kexpr_const_name (kapp_fn a)) (OptionType.some Name nm) -> C) ",
        "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name nm)) => ",
        "ihf (Eq.subst KExpr (fun (x : KExpr) => Eq (OptionType Name) (kexpr_const_name x) (OptionType.some Name nm)) (kapp_fn (KExpr.app f a)) (kapp_fn f) (kapp_fn_app f a) g)) ",
        // lam arm: discharge
        "(fun (ty : KExpr) (ty' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_p env ty ty') (_hbody : par_reduces_p env body body') ",
        "(_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> C) ",
        "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) ",
        "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name nm)) => ",
        "option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.lam ty body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
        // pi arm: discharge
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_p env dom dom') (_hbody : par_reduces_p env body body') ",
        "(_ihd : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name nm) -> C) ",
        "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) ",
        "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name nm)) => ",
        "option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.pi dom body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
        // forall_ arm: discharge
        "(fun (dom : KExpr) (dom' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hd : par_reduces_p env dom dom') (_hbody : par_reduces_p env body body') ",
        "(_ihd : Eq (OptionType Name) (kexpr_const_name (kapp_fn dom)) (OptionType.some Name nm) -> C) ",
        "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) ",
        "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name nm)) => ",
        "option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.forall_ dom body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
        // let_ arm: discharge
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') (_hbody : par_reduces_p env body body') ",
        "(_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> C) ",
        "(_ihval : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name nm) -> C) ",
        "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) ",
        "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm)) => ",
        "option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
        // iota_p arm: e0 ⇒_p e2 (he), iota_step env e2 r (hi); whole step e0 ⇒_p r.
        // Forward the reduced-form fire into kiota (the guard on e0 is irrelevant).
        "(fun (e0 : KExpr) (e2 : KExpr) (r : KExpr) ",
        "(_he : par_reduces_p env e0 e2) (hi : iota_step env e2 r) ",
        "(_ihe : Eq (OptionType Name) (kexpr_const_name (kapp_fn e0)) (OptionType.some Name nm) -> C) ",
        "(_g : Eq (OptionType Name) (kexpr_const_name (kapp_fn e0)) (OptionType.some Name nm)) => ",
        "kiota e2 r hi) ",
        // let_cong arm (trailing congruence): a let is its own spine head (const_name = none) — discharge
        "(fun (ty : KExpr) (ty' : KExpr) (val : KExpr) (val' : KExpr) (body : KExpr) (body' : KExpr) ",
        "(_hty : par_reduces_p env ty ty') (_hval : par_reduces_p env val val') (_hbody : par_reduces_p env body body') ",
        "(_ihty : Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> C) ",
        "(_ihval : Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (OptionType.some Name nm) -> C) ",
        "(_ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> C) ",
        "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm)) => ",
        "option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty val body))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
        // proj arm (trailing congruence): a proj is its own spine head (const_name = none) — discharge
        "(fun (s : Name) (i : Nat) (sub : KExpr) (sub' : KExpr) ",
        "(_hsub : par_reduces_p env sub sub') ",
        "(_ihsub : Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (OptionType.some Name nm) -> C) ",
        "(g : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.some Name nm)) => ",
        "option_none_ne_some Name nm C (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.some Name nm) (Eq.refl (OptionType Name) (OptionType.none Name)) g)) ",
        // scrutinee + apply the head guard
        "e e' h hhead"
    )
    .to_string()
}

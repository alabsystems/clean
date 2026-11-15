// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic-universe replacement for the actual computational parallel model.
//!
//! Every reduct is constructed by induction on the existing reduction relation.
//! This does not assert source correspondence or production iota completeness.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_semantic_parallel_compat(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def ParUniverseTransport (R : RedEnv) (e : KExpr) (r : KExpr) (C : Type) : Type :=
 forall (target : KExpr), KExprUniverseEq e target ->
 (forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq r out -> C) -> C",
            "Continuation package for a constructed corresponding raw parallel reduct. The output step and universe relation are conclusions, not premises.",
        )?;
        self.add_recursive_def(
            r"def par_reduces_cd_universe_compat_at (R : RedEnv) (resultType : Type) (e : KExpr) (r : KExpr)
 (h : par_reduces_cd R e r) : ParUniverseTransport R e r resultType :=
 par_reduces_cd.rec R
 (fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd R x y) => ParUniverseTransport R x y resultType)
 (fun (e : KExpr) => fun (target : KExpr) (h : KExprUniverseEq e target)  (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq e out -> resultType) => k target (par_reduces_cd.refl R target) h)
 (fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (a : KExpr) (a' : KExpr)
 (_pA : par_reduces_cd R A A') (_pb : par_reduces_cd R b b') (_pa : par_reduces_cd R a a')
 (ihA : ParUniverseTransport R A A' resultType) (ihb : ParUniverseTransport R b b' resultType) (iha : ParUniverseTransport R a a' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.app (KExpr.lam A b) a) target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq (instantiate b' a') out -> resultType) =>
 kexprUniverseEq_view (KExpr.app (KExpr.lam A b) a) target h resultType
 (fun (f2 : KExpr) (a2 : KExpr) (hf : KExprUniverseEq (KExpr.lam A b) f2) (ha : KExprUniverseEq a a2)
 (htarget : Eq KExpr target (KExpr.app f2 a2)) =>
 kexprUniverseEq_view (KExpr.lam A b) f2 hf resultType
 (fun (A2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2)
 (hf2 : Eq KExpr f2 (KExpr.lam A2 b2)) =>
 ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cd R A2 A3) (_qA : KExprUniverseEq A' A3) =>
 ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cd R b2 b3) (qb : KExprUniverseEq b' b3) =>
 iha a2 ha (fun (a3 : KExpr) (pa : par_reduces_cd R a2 a3) (qa : KExprUniverseEq a' a3) =>
 k (instantiate b3 a3)
 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R z (instantiate b3 a3))
 (KExpr.app f2 a2) target (Eq.symm KExpr target (KExpr.app f2 a2) htarget)
 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R (KExpr.app z a2) (instantiate b3 a3))
 (KExpr.lam A2 b2) f2 (Eq.symm KExpr f2 (KExpr.lam A2 b2) hf2)
 (par_reduces_cd.beta R A2 A3 b2 b3 a2 a3 pA pb pa)))
 (kexprUniverseEq_instantiate b' b3 qb a' a3 qa)))))))
 (fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (_pf : par_reduces_cd R f f') (_pa : par_reduces_cd R a a') (ihf : ParUniverseTransport R f f' resultType) (iha : ParUniverseTransport R a a' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.app f a) target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq (KExpr.app f' a') out -> resultType) =>
 kexprUniverseEq_view (KExpr.app f a) target h resultType
 (fun (f2 : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (htarget : Eq KExpr target (KExpr.app f2 a2)) => ihf f2 hf (fun (f3 : KExpr) (pf : par_reduces_cd R f2 f3) (qf : KExprUniverseEq f' f3) => iha a2 ha (fun (a3 : KExpr) (pa : par_reduces_cd R a2 a3) (qa : KExprUniverseEq a' a3) => k (KExpr.app f3 a3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R z (KExpr.app f3 a3)) (KExpr.app f2 a2) target (Eq.symm KExpr target (KExpr.app f2 a2) htarget) (par_reduces_cd.app R f2 f3 a2 a3 pf pa)) (KExprUniverseEq.app f' f3 a' a3 qf qa)))))
 (fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (_pA : par_reduces_cd R A A') (_pb : par_reduces_cd R b b') (ihA : ParUniverseTransport R A A' resultType) (ihb : ParUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.lam A b) target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq (KExpr.lam A' b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.lam A b) target h resultType
 (fun (A2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (htarget : Eq KExpr target (KExpr.lam A2 b2)) => ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cd R A2 A3) (qA : KExprUniverseEq A' A3) => ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cd R b2 b3) (qb : KExprUniverseEq b' b3) => k (KExpr.lam A3 b3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R z (KExpr.lam A3 b3)) (KExpr.lam A2 b2) target (Eq.symm KExpr target (KExpr.lam A2 b2) htarget) (par_reduces_cd.lam R A2 A3 b2 b3 pA pb)) (KExprUniverseEq.lam A' A3 b' b3 qA qb)))))
 (fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (_pA : par_reduces_cd R A A') (_pb : par_reduces_cd R b b') (ihA : ParUniverseTransport R A A' resultType) (ihb : ParUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.pi A b) target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq (KExpr.pi A' b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.pi A b) target h resultType
 (fun (A2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (htarget : Eq KExpr target (KExpr.pi A2 b2)) => ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cd R A2 A3) (qA : KExprUniverseEq A' A3) => ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cd R b2 b3) (qb : KExprUniverseEq b' b3) => k (KExpr.pi A3 b3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R z (KExpr.pi A3 b3)) (KExpr.pi A2 b2) target (Eq.symm KExpr target (KExpr.pi A2 b2) htarget) (par_reduces_cd.pi R A2 A3 b2 b3 pA pb)) (KExprUniverseEq.pi A' A3 b' b3 qA qb)))))
 (fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (_pA : par_reduces_cd R A A') (_pb : par_reduces_cd R b b') (ihA : ParUniverseTransport R A A' resultType) (ihb : ParUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.forall_ A b) target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq (KExpr.forall_ A' b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.forall_ A b) target h resultType
 (fun (A2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (htarget : Eq KExpr target (KExpr.forall_ A2 b2)) => ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cd R A2 A3) (qA : KExprUniverseEq A' A3) => ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cd R b2 b3) (qb : KExprUniverseEq b' b3) => k (KExpr.forall_ A3 b3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R z (KExpr.forall_ A3 b3)) (KExpr.forall_ A2 b2) target (Eq.symm KExpr target (KExpr.forall_ A2 b2) htarget) (par_reduces_cd.forall_ R A2 A3 b2 b3 pA pb)) (KExprUniverseEq.pi A' A3 b' b3 qA qb)))))
 (fun (A : KExpr) (A' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr)
 (_pA : par_reduces_cd R A A') (_pv : par_reduces_cd R v v') (_pb : par_reduces_cd R b b')
 (ihA : ParUniverseTransport R A A' resultType) (ihv : ParUniverseTransport R v v' resultType) (ihb : ParUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.let_ A v b) target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq (instantiate b' v') out -> resultType) =>
 kexprUniverseEq_view (KExpr.let_ A v b) target h resultType
 (fun (A2 : KExpr) (v2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2)
 (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (htarget : Eq KExpr target (KExpr.let_ A2 v2 b2)) =>
 ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cd R A2 A3) (_qA : KExprUniverseEq A' A3) =>
 ihv v2 hv (fun (v3 : KExpr) (pv : par_reduces_cd R v2 v3) (qv : KExprUniverseEq v' v3) =>
 ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cd R b2 b3) (qb : KExprUniverseEq b' b3) =>
 k (instantiate b3 v3)
 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R z (instantiate b3 v3)) (KExpr.let_ A2 v2 b2) target (Eq.symm KExpr target (KExpr.let_ A2 v2 b2) htarget) (par_reduces_cd.let_ R A2 A3 v2 v3 b2 b3 pA pv pb))
 (kexprUniverseEq_instantiate b' b3 qb v' v3 qv))))))
 (fun (e : KExpr) (r : KExpr) (step : iota_step (red_rec R) e r) =>
 fun (target : KExpr) (h : KExprUniverseEq e target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq r out -> resultType) =>
 iota_reduct_universe_compat (red_rec R) e target r h step resultType
 (fun (out : KExpr) (p : iota_step (red_rec R) target out) (q : KExprUniverseEq r out) =>
 k out (par_reduces_cd.iota R target out p) q))
 (fun (e : KExpr) (r : KExpr) (step : delta_step (red_def R) e r) =>
 fun (target : KExpr) (h : KExprUniverseEq e target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq r out -> resultType) =>
 delta_reduct_semantic_compat (red_def R) e target h r step resultType
 (fun (out : KExpr) (p : delta_step (red_def R) target out) (q : KExprUniverseEq r out) =>
 k out (par_reduces_cd.delta R target out p) q))
 (fun (A : KExpr) (A' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr) (_pA : par_reduces_cd R A A') (_pv : par_reduces_cd R v v') (_pb : par_reduces_cd R b b') (ihA : ParUniverseTransport R A A' resultType) (ihv : ParUniverseTransport R v v' resultType) (ihb : ParUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.let_ A v b) target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq (KExpr.let_ A' v' b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.let_ A v b) target h resultType
 (fun (A2 : KExpr) (v2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (htarget : Eq KExpr target (KExpr.let_ A2 v2 b2)) => ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cd R A2 A3) (qA : KExprUniverseEq A' A3) => ihv v2 hv (fun (v3 : KExpr) (pv : par_reduces_cd R v2 v3) (qv : KExprUniverseEq v' v3) => ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cd R b2 b3) (qb : KExprUniverseEq b' b3) => k (KExpr.let_ A3 v3 b3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R z (KExpr.let_ A3 v3 b3)) (KExpr.let_ A2 v2 b2) target (Eq.symm KExpr target (KExpr.let_ A2 v2 b2) htarget) (par_reduces_cd.let_cong R A2 A3 v2 v3 b2 b3 pA pv pb)) (KExprUniverseEq.let_ A' A3 v' v3 b' b3 qA qv qb))))))
 (fun (n : Name) (i : Nat) (b : KExpr) (b' : KExpr)
 (_pb : par_reduces_cd R b b') (ihb : ParUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.proj n i b) target)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq (KExpr.proj n i b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.proj n i b) target h resultType
 (fun (b2 : KExpr) (hb : KExprUniverseEq b b2) (htarget : Eq KExpr target (KExpr.proj n i b2)) =>
 ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cd R b2 b3) (qb : KExprUniverseEq b' b3) =>
 k (KExpr.proj n i b3)
 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R z (KExpr.proj n i b3)) (KExpr.proj n i b2) target (Eq.symm KExpr target (KExpr.proj n i b2) htarget) (par_reduces_cd.proj R n i b2 b3 pb))
 (KExprUniverseEq.proj n i b' b3 qb)))) e r h",
            "All eleven actual computational-parallel constructors preserve semantic universe replacement in their source. Beta and zeta use actual substitution compatibility; delta and iota use proved operational graph compatibility. No environment support, confluence, typing or source-refinement assumption is carried.",
        )?;

        self.add_recursive_def(
            r"def par_reduces_cd_universe_compat (R : RedEnv) (e : KExpr) (r : KExpr)
 (h : par_reduces_cd R e r) (target : KExpr) (related : KExprUniverseEq e target) (C : Type)
 (k : forall (out : KExpr), par_reduces_cd R target out -> KExprUniverseEq r out -> C) : C :=
 par_reduces_cd_universe_compat_at R C e r h target related k",
            "Public continuation interface; the induction fixes the result type outside its motive and derives both the replacement trace and semantic result.",
        )?;
        self.add_recursive_def(
            r"def ParStarUniverseTransport (R : RedEnv) (e : KExpr) (r : KExpr) (C : Type) : Type :=
 forall (target : KExpr), KExprUniverseEq e target ->
 (forall (out : KExpr), par_reduces_cd_star R target out -> KExprUniverseEq r out -> C) -> C",
            "Continuation package for a constructed corresponding finite raw parallel trace.",
        )?;
        self.add_recursive_def(
            r"def par_reduces_cd_star_universe_compat_at (R : RedEnv) (resultType : Type) (e : KExpr) (r : KExpr)
 (h : par_reduces_cd_star R e r) : ParStarUniverseTransport R e r resultType :=
 par_reduces_cd_star.rec R
 (fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd_star R x y) => ParStarUniverseTransport R x y resultType)
 (fun (x : KExpr) => fun (target : KExpr) (hxy : KExprUniverseEq x target)
 (k : forall (out : KExpr), par_reduces_cd_star R target out -> KExprUniverseEq x out -> resultType) =>
 k target (par_reduces_cd_star.refl R target) hxy)
 (fun (x : KExpr) (y : KExpr) (z : KExpr) (step : par_reduces_cd R x y)
 (_tail : par_reduces_cd_star R y z) (ih : ParStarUniverseTransport R y z resultType) =>
 fun (target : KExpr) (hxt : KExprUniverseEq x target)
 (k : forall (out : KExpr), par_reduces_cd_star R target out -> KExprUniverseEq z out -> resultType) =>
 par_reduces_cd_universe_compat R x y step target hxt resultType
 (fun (middle : KExpr) (first : par_reduces_cd R target middle) (hym : KExprUniverseEq y middle) =>
 ih middle hym
 (fun (out : KExpr) (rest : par_reduces_cd_star R middle out) (hzo : KExprUniverseEq z out) =>
 k out (par_reduces_cd_star.step R target middle out first rest) hzo))) e r h",
            "Finite raw traces preserve semantic universe replacement by actual trace induction and the checked one-step theorem. No termination or confluence hypothesis.",
        )?;

        self.add_recursive_def(
            r"def par_reduces_cd_star_universe_compat (R : RedEnv) (e : KExpr) (r : KExpr)
 (h : par_reduces_cd_star R e r) (target : KExpr) (related : KExprUniverseEq e target) (C : Type)
 (k : forall (out : KExpr), par_reduces_cd_star R target out -> KExprUniverseEq r out -> C) : C :=
 par_reduces_cd_star_universe_compat_at R C e r h target related k",
            "Public continuation interface; the induction fixes the result type outside its motive and derives both the replacement trace and semantic result.",
        )?;
        self.add_recursive_def(
            r"def semantic_parallel_beta_caller (R : RedEnv) (u : Level) :
 forall (C : Type), (forall (out : KExpr),
 par_reduces_cd R (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) out -> KExprUniverseEq (KExpr.sort (Level.imax u Level.zero)) out -> C) -> C :=
 fun (C : Type) (k : forall (out : KExpr),
 par_reduces_cd R (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) out -> KExprUniverseEq (KExpr.sort (Level.imax u Level.zero)) out -> C) =>
 par_reduces_cd_universe_compat R (KExpr.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.sort (Level.imax u Level.zero))) (KExpr.sort (Level.imax u Level.zero)) (par_reduces_cd.beta R (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (par_reduces_cd.refl R (KExpr.sort (Level.imax u Level.zero))) (par_reduces_cd.refl R (KExpr.bvar Nat.zero)) (par_reduces_cd.refl R (KExpr.sort (Level.imax u Level.zero))))
 (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) (KExprUniverseEq.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero) (KExprUniverseEq.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (kexprUniverseEq_imax_zero u) (KExprUniverseEq.bvar Nat.zero)) (kexprUniverseEq_imax_zero u)) C k",
            "An actual beta step under arbitrary R transports non-syntactically equal universe annotations and arguments, constructing a corresponding step.",
        )?;
        self.add_recursive_def(
            r"def semantic_parallel_two_step_caller (R : RedEnv) (u : Level) :
 forall (C : Type), (forall (out : KExpr),
 par_reduces_cd_star R (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))) out -> KExprUniverseEq (KExpr.sort (Level.imax u Level.zero)) out -> C) -> C :=
 fun (C : Type) (k : forall (out : KExpr),
 par_reduces_cd_star R (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))) out -> KExprUniverseEq (KExpr.sort (Level.imax u Level.zero)) out -> C) =>
 par_reduces_cd_star_universe_compat R (KExpr.let_ (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (KExpr.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))) (KExpr.sort (Level.imax u Level.zero))
 (par_reduces_cd_star.step R (KExpr.let_ (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (KExpr.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))) (KExpr.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.sort (Level.imax u Level.zero))) (KExpr.sort (Level.imax u Level.zero)) (par_reduces_cd.let_ R (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (KExpr.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)) (par_reduces_cd.refl R (KExpr.sort (Level.imax u Level.zero))) (par_reduces_cd.refl R (KExpr.sort (Level.imax u Level.zero))) (par_reduces_cd.refl R (KExpr.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))))
 (par_reduces_cd_star.step R (KExpr.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.sort (Level.imax u Level.zero))) (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (par_reduces_cd.beta R (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort (Level.imax u Level.zero)) (par_reduces_cd.refl R (KExpr.sort (Level.imax u Level.zero))) (par_reduces_cd.refl R (KExpr.bvar Nat.zero)) (par_reduces_cd.refl R (KExpr.sort (Level.imax u Level.zero))))
 (par_reduces_cd_star.refl R (KExpr.sort (Level.imax u Level.zero)))))
 (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))) (KExprUniverseEq.let_ (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero) (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero) (KExpr.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)) (kexprUniverseEq_imax_zero u) (kexprUniverseEq_imax_zero u) (KExprUniverseEq.app (KExpr.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.bvar Nat.zero)) (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (KExprUniverseEq.lam (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (kexprUniverseEq_imax_zero u) (KExprUniverseEq.bvar Nat.zero)) (KExprUniverseEq.bvar Nat.zero))) C k",
            "An actual zeta-then-beta trace transports a semantic universe change throughout the let, lambda annotation and substituted argument. Both trace steps are constructed.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn semantic_parallel_and_star_transport_are_kernel_checked() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "ParUniverseTransport",
            "par_reduces_cd_universe_compat_at",
            "par_reduces_cd_universe_compat",
            "ParStarUniverseTransport",
            "par_reduces_cd_star_universe_compat_at",
            "par_reduces_cd_star_universe_compat",
            "semantic_parallel_beta_caller",
            "semantic_parallel_two_step_caller",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("checked transport proof");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }
}

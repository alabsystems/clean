// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection-aware semantic conversion: universe.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "CDPUniverseTransport",
        r"forall (R : RedEnv) (e : KExpr) (r : KExpr) (C : Type), Type",
        r"fun (R : RedEnv) (e : KExpr) (r : KExpr) (C : Type) => forall (target : KExpr), KExprUniverseEq e target ->
 (forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq r out -> C) -> C",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_universe_compat_at",
        r"forall (R : RedEnv) (resultType : Type) (e : KExpr) (r : KExpr)
 (h : par_reduces_cdp R e r), CDPUniverseTransport R e r resultType",
        r"fun (R : RedEnv) (resultType : Type) (e : KExpr) (r : KExpr)
 (h : par_reduces_cdp R e r) => @par_reduces_cdp.rec R
 (fun (x : KExpr) (y : KExpr) (_h : par_reduces_cdp R x y) => CDPUniverseTransport R x y resultType)
 (fun (e : KExpr) => fun (target : KExpr) (h : KExprUniverseEq e target)  (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq e out -> resultType) => k target (@par_reduces_cdp.refl R target) h)
 (fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (a : KExpr) (a' : KExpr)
 (_pA : par_reduces_cdp R A A') (_pb : par_reduces_cdp R b b') (_pa : par_reduces_cdp R a a')
 (ihA : CDPUniverseTransport R A A' resultType) (ihb : CDPUniverseTransport R b b' resultType) (iha : CDPUniverseTransport R a a' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.app (KExpr.lam A b) a) target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq (instantiate b' a') out -> resultType) =>
 kexprUniverseEq_view (KExpr.app (KExpr.lam A b) a) target h resultType
 (fun (f2 : KExpr) (a2 : KExpr) (hf : KExprUniverseEq (KExpr.lam A b) f2) (ha : KExprUniverseEq a a2)
 (htarget : @Eq KExpr target (KExpr.app f2 a2)) =>
 kexprUniverseEq_view (KExpr.lam A b) f2 hf resultType
 (fun (A2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2)
 (hf2 : @Eq KExpr f2 (KExpr.lam A2 b2)) =>
 ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cdp R A2 A3) (_qA : KExprUniverseEq A' A3) =>
 ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cdp R b2 b3) (qb : KExprUniverseEq b' b3) =>
 iha a2 ha (fun (a3 : KExpr) (pa : par_reduces_cdp R a2 a3) (qa : KExprUniverseEq a' a3) =>
 k (instantiate b3 a3)
 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R z (instantiate b3 a3))
 (KExpr.app f2 a2) target (Eq.symm KExpr target (KExpr.app f2 a2) htarget)
 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R (KExpr.app z a2) (instantiate b3 a3))
 (KExpr.lam A2 b2) f2 (Eq.symm KExpr f2 (KExpr.lam A2 b2) hf2)
 (@par_reduces_cdp.beta R A2 A3 b2 b3 a2 a3 pA pb pa)))
 (kexprUniverseEq_instantiate b' b3 qb a' a3 qa)))))))
 (fun (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr) (_pf : par_reduces_cdp R f f') (_pa : par_reduces_cdp R a a') (ihf : CDPUniverseTransport R f f' resultType) (iha : CDPUniverseTransport R a a' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.app f a) target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq (KExpr.app f' a') out -> resultType) =>
 kexprUniverseEq_view (KExpr.app f a) target h resultType
 (fun (f2 : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (htarget : @Eq KExpr target (KExpr.app f2 a2)) => ihf f2 hf (fun (f3 : KExpr) (pf : par_reduces_cdp R f2 f3) (qf : KExprUniverseEq f' f3) => iha a2 ha (fun (a3 : KExpr) (pa : par_reduces_cdp R a2 a3) (qa : KExprUniverseEq a' a3) => k (KExpr.app f3 a3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R z (KExpr.app f3 a3)) (KExpr.app f2 a2) target (Eq.symm KExpr target (KExpr.app f2 a2) htarget) (@par_reduces_cdp.app R f2 f3 a2 a3 pf pa)) (KExprUniverseEq.app f' f3 a' a3 qf qa)))))
 (fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (_pA : par_reduces_cdp R A A') (_pb : par_reduces_cdp R b b') (ihA : CDPUniverseTransport R A A' resultType) (ihb : CDPUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.lam A b) target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq (KExpr.lam A' b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.lam A b) target h resultType
 (fun (A2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (htarget : @Eq KExpr target (KExpr.lam A2 b2)) => ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cdp R A2 A3) (qA : KExprUniverseEq A' A3) => ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cdp R b2 b3) (qb : KExprUniverseEq b' b3) => k (KExpr.lam A3 b3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R z (KExpr.lam A3 b3)) (KExpr.lam A2 b2) target (Eq.symm KExpr target (KExpr.lam A2 b2) htarget) (@par_reduces_cdp.lam R A2 A3 b2 b3 pA pb)) (KExprUniverseEq.lam A' A3 b' b3 qA qb)))))
 (fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (_pA : par_reduces_cdp R A A') (_pb : par_reduces_cdp R b b') (ihA : CDPUniverseTransport R A A' resultType) (ihb : CDPUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.pi A b) target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq (KExpr.pi A' b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.pi A b) target h resultType
 (fun (A2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (htarget : @Eq KExpr target (KExpr.pi A2 b2)) => ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cdp R A2 A3) (qA : KExprUniverseEq A' A3) => ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cdp R b2 b3) (qb : KExprUniverseEq b' b3) => k (KExpr.pi A3 b3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R z (KExpr.pi A3 b3)) (KExpr.pi A2 b2) target (Eq.symm KExpr target (KExpr.pi A2 b2) htarget) (@par_reduces_cdp.pi R A2 A3 b2 b3 pA pb)) (KExprUniverseEq.pi A' A3 b' b3 qA qb)))))
 (fun (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr) (_pA : par_reduces_cdp R A A') (_pb : par_reduces_cdp R b b') (ihA : CDPUniverseTransport R A A' resultType) (ihb : CDPUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.forall_ A b) target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq (KExpr.forall_ A' b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.forall_ A b) target h resultType
 (fun (A2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (htarget : @Eq KExpr target (KExpr.forall_ A2 b2)) => ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cdp R A2 A3) (qA : KExprUniverseEq A' A3) => ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cdp R b2 b3) (qb : KExprUniverseEq b' b3) => k (KExpr.forall_ A3 b3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R z (KExpr.forall_ A3 b3)) (KExpr.forall_ A2 b2) target (Eq.symm KExpr target (KExpr.forall_ A2 b2) htarget) (@par_reduces_cdp.forall_ R A2 A3 b2 b3 pA pb)) (KExprUniverseEq.pi A' A3 b' b3 qA qb)))))
 (fun (A : KExpr) (A' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr)
 (_pA : par_reduces_cdp R A A') (_pv : par_reduces_cdp R v v') (_pb : par_reduces_cdp R b b')
 (ihA : CDPUniverseTransport R A A' resultType) (ihv : CDPUniverseTransport R v v' resultType) (ihb : CDPUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.let_ A v b) target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq (instantiate b' v') out -> resultType) =>
 kexprUniverseEq_view (KExpr.let_ A v b) target h resultType
 (fun (A2 : KExpr) (v2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2)
 (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (htarget : @Eq KExpr target (KExpr.let_ A2 v2 b2)) =>
 ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cdp R A2 A3) (_qA : KExprUniverseEq A' A3) =>
 ihv v2 hv (fun (v3 : KExpr) (pv : par_reduces_cdp R v2 v3) (qv : KExprUniverseEq v' v3) =>
 ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cdp R b2 b3) (qb : KExprUniverseEq b' b3) =>
 k (instantiate b3 v3)
 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R z (instantiate b3 v3)) (KExpr.let_ A2 v2 b2) target (Eq.symm KExpr target (KExpr.let_ A2 v2 b2) htarget) (@par_reduces_cdp.let_ R A2 A3 v2 v3 b2 b3 pA pv pb))
 (kexprUniverseEq_instantiate b' b3 qb v' v3 qv))))))
 (fun (e : KExpr) (r : KExpr) (step : iota_step (red_rec R) e r) =>
 fun (target : KExpr) (h : KExprUniverseEq e target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq r out -> resultType) =>
 iota_reduct_universe_compat (red_rec R) e target r h step resultType
 (fun (out : KExpr) (p : iota_step (red_rec R) target out) (q : KExprUniverseEq r out) =>
 k out (@par_reduces_cdp.iota R target out p) q))
 (fun (e : KExpr) (r : KExpr) (step : delta_step (red_def R) e r) =>
 fun (target : KExpr) (h : KExprUniverseEq e target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq r out -> resultType) =>
 delta_reduct_semantic_compat (red_def R) e target h r step resultType
 (fun (out : KExpr) (p : delta_step (red_def R) target out) (q : KExprUniverseEq r out) =>
 k out (@par_reduces_cdp.delta R target out p) q))
 (fun (A : KExpr) (A' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr) (_pA : par_reduces_cdp R A A') (_pv : par_reduces_cdp R v v') (_pb : par_reduces_cdp R b b') (ihA : CDPUniverseTransport R A A' resultType) (ihv : CDPUniverseTransport R v v' resultType) (ihb : CDPUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.let_ A v b) target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq (KExpr.let_ A' v' b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.let_ A v b) target h resultType
 (fun (A2 : KExpr) (v2 : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (htarget : @Eq KExpr target (KExpr.let_ A2 v2 b2)) => ihA A2 hA (fun (A3 : KExpr) (pA : par_reduces_cdp R A2 A3) (qA : KExprUniverseEq A' A3) => ihv v2 hv (fun (v3 : KExpr) (pv : par_reduces_cdp R v2 v3) (qv : KExprUniverseEq v' v3) => ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cdp R b2 b3) (qb : KExprUniverseEq b' b3) => k (KExpr.let_ A3 v3 b3) (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R z (KExpr.let_ A3 v3 b3)) (KExpr.let_ A2 v2 b2) target (Eq.symm KExpr target (KExpr.let_ A2 v2 b2) htarget) (@par_reduces_cdp.let_cong R A2 A3 v2 v3 b2 b3 pA pv pb)) (KExprUniverseEq.let_ A' A3 v' v3 b' b3 qA qv qb))))))
 (fun (n : Name) (i : Nat) (b : KExpr) (b' : KExpr)
 (_pb : par_reduces_cdp R b b') (ihb : CDPUniverseTransport R b b' resultType) =>
 fun (target : KExpr) (h : KExprUniverseEq (KExpr.proj n i b) target)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq (KExpr.proj n i b') out -> resultType) =>
 kexprUniverseEq_view (KExpr.proj n i b) target h resultType
 (fun (b2 : KExpr) (hb : KExprUniverseEq b b2) (htarget : @Eq KExpr target (KExpr.proj n i b2)) =>
 ihb b2 hb (fun (b3 : KExpr) (pb : par_reduces_cdp R b2 b3) (qb : KExprUniverseEq b' b3) =>
 k (KExpr.proj n i b3)
 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cdp R z (KExpr.proj n i b3)) (KExpr.proj n i b2) target (Eq.symm KExpr target (KExpr.proj n i b2) htarget) (@par_reduces_cdp.proj R n i b2 b3 pb))
 (KExprUniverseEq.proj n i b' b3 qb))))
 (fun (S : Name) (idx : Nat) (subject : KExpr) (result : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (@OptionType.some KExpr result)) =>
 fun (target : KExpr) (related : KExprUniverseEq (KExpr.proj S idx subject) target)
 (next : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq result out -> resultType) =>
 kexprUniverseEq_view (KExpr.proj S idx subject) target related resultType
  (fun (subject2 : KExpr) (subjects : KExprUniverseEq subject subject2)
   (target_eq : @Eq KExpr target (KExpr.proj S idx subject2)) =>
   projection_post_whnf_universe_compat R S idx subject subject2 subjects result run resultType
    (fun (out : KExpr)
     (run2 : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (@OptionType.some KExpr out))
     (outputs : KExprUniverseEq result out) =>
     next out
      (Eq.substType KExpr (fun (origin : KExpr) => par_reduces_cdp R origin out)
       (KExpr.proj S idx subject2) target (Eq.symm KExpr target (KExpr.proj S idx subject2) target_eq)
       (@par_reduces_cdp.projection_beta R S idx subject2 out run2)) outputs))) e r h",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_universe_compat",
        r"forall (R : RedEnv) (e : KExpr) (r : KExpr)
 (h : par_reduces_cdp R e r) (target : KExpr) (related : KExprUniverseEq e target) (C : Type)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq r out -> C), C",
        r"fun (R : RedEnv) (e : KExpr) (r : KExpr)
 (h : par_reduces_cdp R e r) (target : KExpr) (related : KExprUniverseEq e target) (C : Type)
 (k : forall (out : KExpr), par_reduces_cdp R target out -> KExprUniverseEq r out -> C) => par_reduces_cdp_universe_compat_at R C e r h target related k",
    ),
    DeclarationInput::Data(
        "CDPStarUniverseTransport",
        r"forall (R : RedEnv) (e : KExpr) (r : KExpr) (C : Type), Type",
        r"fun (R : RedEnv) (e : KExpr) (r : KExpr) (C : Type) => forall (target : KExpr), KExprUniverseEq e target ->
 (forall (out : KExpr), par_reduces_cdp_star R target out -> KExprUniverseEq r out -> C) -> C",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_universe_compat_at",
        r"forall (R : RedEnv) (resultType : Type) (e : KExpr) (r : KExpr)
 (h : par_reduces_cdp_star R e r), CDPStarUniverseTransport R e r resultType",
        r"fun (R : RedEnv) (resultType : Type) (e : KExpr) (r : KExpr)
 (h : par_reduces_cdp_star R e r) => @par_reduces_cdp_star.rec R
 (fun (x : KExpr) (y : KExpr) (_h : par_reduces_cdp_star R x y) => CDPStarUniverseTransport R x y resultType)
 (fun (x : KExpr) => fun (target : KExpr) (hxy : KExprUniverseEq x target)
 (k : forall (out : KExpr), par_reduces_cdp_star R target out -> KExprUniverseEq x out -> resultType) =>
 k target (@par_reduces_cdp_star.refl R target) hxy)
 (fun (x : KExpr) (y : KExpr) (z : KExpr) (step : par_reduces_cdp R x y)
 (_tail : par_reduces_cdp_star R y z) (ih : CDPStarUniverseTransport R y z resultType) =>
 fun (target : KExpr) (hxt : KExprUniverseEq x target)
 (k : forall (out : KExpr), par_reduces_cdp_star R target out -> KExprUniverseEq z out -> resultType) =>
 par_reduces_cdp_universe_compat R x y step target hxt resultType
 (fun (middle : KExpr) (first : par_reduces_cdp R target middle) (hym : KExprUniverseEq y middle) =>
 ih middle hym
 (fun (out : KExpr) (rest : par_reduces_cdp_star R middle out) (hzo : KExprUniverseEq z out) =>
 k out (@par_reduces_cdp_star.step R target middle out first rest) hzo))) e r h",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_universe_compat",
        r"forall (R : RedEnv) (e : KExpr) (r : KExpr)
 (h : par_reduces_cdp_star R e r) (target : KExpr) (related : KExprUniverseEq e target) (C : Type)
 (k : forall (out : KExpr), par_reduces_cdp_star R target out -> KExprUniverseEq r out -> C), C",
        r"fun (R : RedEnv) (e : KExpr) (r : KExpr)
 (h : par_reduces_cdp_star R e r) (target : KExpr) (related : KExprUniverseEq e target) (C : Type)
 (k : forall (out : KExpr), par_reduces_cdp_star R target out -> KExprUniverseEq r out -> C) => par_reduces_cdp_star_universe_compat_at R C e r h target related k",
    ),
    DeclarationInput::Data(
        "cdp_universe_projection",
        r"forall (u : Level), KExpr",
        r"fun (u : Level) => KExpr.proj kcre_prod_type_name Nat.zero (projection_universe_subject u)",
    ),
    DeclarationInput::Proof(
        "cdp_universe_projection_select",
        r"forall (u : Level), @Eq (OptionType KExpr) (projection_post_whnf_reduct the_red_env (cdp_universe_projection u))
 (@OptionType.some KExpr (KExpr.sort u))",
        r"fun (u : Level) => @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort u))",
    ),
    DeclarationInput::Proof(
        "cdp_universe_projection_step",
        r"forall (u : Level), par_reduces_cdp the_red_env (cdp_universe_projection u) (KExpr.sort u)",
        r"fun (u : Level) => @par_reduces_cdp.projection_beta the_red_env kcre_prod_type_name Nat.zero
  (projection_universe_subject u) (KExpr.sort u) (cdp_universe_projection_select u)",
    ),
    DeclarationInput::Proof(
        "cdp_universe_projection_related",
        r"forall (u v : Level) (levels : levelEqSem u v), KExprUniverseEq (cdp_universe_projection u) (cdp_universe_projection v)",
        r"fun (u v : Level) (levels : levelEqSem u v) => KExprUniverseEq.proj kcre_prod_type_name Nat.zero (projection_universe_subject u) (projection_universe_subject v)
  (KExprUniverseEq.app
   (KExpr.app ctor_spine_prod_prefix (KExpr.sort u)) (KExpr.app ctor_spine_prod_prefix (KExpr.sort v))
   rfnz_zero rfnz_zero
   (KExprUniverseEq.app ctor_spine_prod_prefix ctor_spine_prod_prefix (KExpr.sort u) (KExpr.sort v)
    (kexprUniverseEq_refl ctor_spine_prod_prefix) (KExprUniverseEq.sort u v levels))
   (kexprUniverseEq_refl rfnz_zero))",
    ),
    DeclarationInput::Proof(
        "cdp_universe_projection_caller",
        r"forall (u v : Level) (levels : levelEqSem u v) (C : Type)
 (next : forall (out : KExpr), par_reduces_cdp the_red_env (cdp_universe_projection v) out ->
  KExprUniverseEq (KExpr.sort u) out -> C), C",
        r"fun (u v : Level) (levels : levelEqSem u v) (C : Type)
 (next : forall (out : KExpr), par_reduces_cdp the_red_env (cdp_universe_projection v) out ->
  KExprUniverseEq (KExpr.sort u) out -> C) => par_reduces_cdp_universe_compat the_red_env (cdp_universe_projection u) (KExpr.sort u)
  (cdp_universe_projection_step u) (cdp_universe_projection v) (cdp_universe_projection_related u v levels) C next",
    ),
    DeclarationInput::Proof(
        "cdp_universe_nonzero_levels",
        r"forall (u : Level), levelEqSem (Level.succ (Level.imax u Level.zero)) (Level.succ Level.zero)",
        r"fun (u : Level) => fun (valuation : Name -> Nat) => @Eq.refl Nat (Nat.succ Nat.zero)",
    ),
    DeclarationInput::Proof(
        "cdp_universe_projection_nonzero",
        r"forall (C : Type)
 (next : forall (out : KExpr), par_reduces_cdp the_red_env (cdp_universe_projection (Level.succ Level.zero)) out ->
  KExprUniverseEq (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))) out -> C), C",
        r"fun (C : Type)
 (next : forall (out : KExpr), par_reduces_cdp the_red_env (cdp_universe_projection (Level.succ Level.zero)) out ->
  KExprUniverseEq (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))) out -> C) => cdp_universe_projection_caller (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))
  (Level.succ Level.zero) (cdp_universe_nonzero_levels (Level.param Name.anonymous)) C next",
    ),
    DeclarationInput::Data(
        "cdp_universe_beta_source",
        r"forall (u : Level), KExpr",
        r"fun (u : Level) => KExpr.app (KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero)) (cdp_universe_projection u)",
    ),
    DeclarationInput::Proof(
        "cdp_universe_beta_parallel",
        r"forall (u : Level), par_reduces_cdp the_red_env (cdp_universe_beta_source u) (KExpr.sort u)",
        r"fun (u : Level) => @par_reduces_cdp.beta the_red_env (KExpr.sort u) (KExpr.sort u) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)
  (cdp_universe_projection u) (KExpr.sort u)
  (@par_reduces_cdp.refl the_red_env (KExpr.sort u)) (@par_reduces_cdp.refl the_red_env (KExpr.bvar Nat.zero))
  (cdp_universe_projection_step u)",
    ),
    DeclarationInput::Proof(
        "cdp_universe_beta_related",
        r"forall (u v : Level) (levels : levelEqSem u v), KExprUniverseEq (cdp_universe_beta_source u) (cdp_universe_beta_source v)",
        r"fun (u v : Level) (levels : levelEqSem u v) => KExprUniverseEq.app
  (KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero)) (KExpr.lam (KExpr.sort v) (KExpr.bvar Nat.zero))
  (cdp_universe_projection u) (cdp_universe_projection v)
  (KExprUniverseEq.lam (KExpr.sort u) (KExpr.sort v) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)
   (KExprUniverseEq.sort u v levels) (KExprUniverseEq.bvar Nat.zero))
  (cdp_universe_projection_related u v levels)",
    ),
    DeclarationInput::Proof(
        "cdp_universe_beta_nonzero_transport",
        r"forall (C : Type)
 (next : forall (out : KExpr), par_reduces_cdp the_red_env (cdp_universe_beta_source (Level.succ Level.zero)) out ->
  KExprUniverseEq (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))) out -> C), C",
        r"fun (C : Type)
 (next : forall (out : KExpr), par_reduces_cdp the_red_env (cdp_universe_beta_source (Level.succ Level.zero)) out ->
  KExprUniverseEq (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))) out -> C) => par_reduces_cdp_universe_compat the_red_env
  (cdp_universe_beta_source (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (cdp_universe_beta_parallel (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (cdp_universe_beta_source (Level.succ Level.zero))
  (cdp_universe_beta_related (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))
   (Level.succ Level.zero) (cdp_universe_nonzero_levels (Level.param Name.anonymous))) C next",
    ),
    DeclarationInput::Proof(
        "cdp_universe_beta_star",
        r"forall (u : Level), par_reduces_cdp_star the_red_env (cdp_universe_beta_source u) (KExpr.sort u)",
        r"fun (u : Level) => @par_reduces_cdp_star.step the_red_env (cdp_universe_beta_source u)
  (KExpr.app (KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero)) (KExpr.sort u)) (KExpr.sort u)
  (@par_reduces_cdp.app the_red_env
   (KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero)) (KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero))
   (cdp_universe_projection u) (KExpr.sort u)
   (@par_reduces_cdp.refl the_red_env (KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero))) (cdp_universe_projection_step u))
  (@par_reduces_cdp_star.step the_red_env
   (KExpr.app (KExpr.lam (KExpr.sort u) (KExpr.bvar Nat.zero)) (KExpr.sort u)) (KExpr.sort u) (KExpr.sort u)
   (@par_reduces_cdp.beta the_red_env (KExpr.sort u) (KExpr.sort u) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)
    (KExpr.sort u) (KExpr.sort u)
    (@par_reduces_cdp.refl the_red_env (KExpr.sort u)) (@par_reduces_cdp.refl the_red_env (KExpr.bvar Nat.zero))
    (@par_reduces_cdp.refl the_red_env (KExpr.sort u)))
   (@par_reduces_cdp_star.refl the_red_env (KExpr.sort u)))",
    ),
    DeclarationInput::Proof(
        "cdp_universe_star_nonzero_transport",
        r"forall (C : Type)
 (next : forall (out : KExpr), par_reduces_cdp_star the_red_env (cdp_universe_beta_source (Level.succ Level.zero)) out ->
  KExprUniverseEq (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))) out -> C), C",
        r"fun (C : Type)
 (next : forall (out : KExpr), par_reduces_cdp_star the_red_env (cdp_universe_beta_source (Level.succ Level.zero)) out ->
  KExprUniverseEq (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))) out -> C) => par_reduces_cdp_star_universe_compat the_red_env
  (cdp_universe_beta_source (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (cdp_universe_beta_star (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (cdp_universe_beta_source (Level.succ Level.zero))
  (cdp_universe_beta_related (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))
   (Level.succ Level.zero) (cdp_universe_nonzero_levels (Level.param Name.anonymous))) C next",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_cdp_universe_raw_equality",
        r"@Eq KExpr (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero))",
        r"@Eq.refl KExpr (KExpr.sort (Level.succ Level.zero))",
    ),
    (
        "forged_cdp_universe_zero_endpoint",
        r"par_reduces_cdp_star the_red_env
  (cdp_universe_beta_source (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort Level.zero)",
        r"cdp_universe_beta_star (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "par_reduces_cdp_universe_compat_at",
    "par_reduces_cdp_universe_compat",
    "par_reduces_cdp_star_universe_compat_at",
    "par_reduces_cdp_star_universe_compat",
    "cdp_universe_projection_select",
    "cdp_universe_projection_step",
    "cdp_universe_projection_related",
    "cdp_universe_projection_caller",
    "cdp_universe_nonzero_levels",
    "cdp_universe_projection_nonzero",
    "cdp_universe_beta_parallel",
    "cdp_universe_beta_related",
    "cdp_universe_beta_nonzero_transport",
    "cdp_universe_beta_star",
    "cdp_universe_star_nonzero_transport",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "CDPUniverseTransport",
    "CDPStarUniverseTransport",
    "cdp_universe_projection",
    "cdp_universe_beta_source",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

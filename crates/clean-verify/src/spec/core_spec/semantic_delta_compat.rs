// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Same-environment semantic universe compatibility for guarded delta lookup
//! and the actual expression-level delta evaluator.
//!
//! The SAME ordered parameter list and schematic body are used on both sides.
//! Related universe lists imply the same guard length, and actual inversion and
//! introduction derive the replacement lookup. There is no assumed output
//! lookup, reduction step, typing judgment, NoDup, body support or closedness.
//!
//! This differs from commuting an arbitrary universe substitution past a FIXED
//! environment: that separate theorem needs stored-body parameter support.
//! It also does not establish Rust's parameter-order/Name representation or
//! first-match versus HashMap last-match agreement; their NoDup/admission and
//! source-reflection obligations remain separate. No iota theorem is added.
//!
//! Registration is deliberately separate from this bounded proof unit.
//!
//! Independent proof-development check: 58 declarations copied from the actual
//! 31fa57c00 Wgxf0r export (SHA256
//! 941dcfb5f386a75f80afef5afc35dfc733e1fde210abea22bbf8ae3333478957),
//! plus the current LevelListEqSem/KExprUniverseEq/levelEqSem_refl definitions.
//! Pinned Lean 4.30.0-rc2 checked all 24 new proof/control declarations with
//! empty actual axiom closures on 2026-09-08 (0.28 seconds, 423,051,264-byte
//! maximum RSS; 1 GB reserved). This does not replace registered Clean checks
//! and full replay after integration.
//!
//! Expression-level extension: 68 exact declarations from that same export,
//! the current semantic relation/lookup declarations and five semantic spine
//! declarations. All 12 new declarations checked axiom-free with pinned Lean
//! 4.30.0-rc2 on 2026-09-08 (0.42 seconds, 434,798,592-byte maximum RSS;
//! 1 GB reserved). Exact scratch SHA256:
//! 7513a5cfdfa6371355cfe1531db96d7056f696bd3e37decf818a3ec5c66d61aa.
//! The forged wrong-arity success control was separately rejected with the
//! expected Eq.refl type mismatch (0.34 seconds, 433,111,040-byte maximum RSS).
//! Integration correction: the latest exact export already provides
//! delta_reduct_some_inv_type; the duplicate local projected inverter was
//! removed and the caller now reuses that actual theorem plus option_some_inj.
//! Root's combined exact-source parallel guide checked this correction and all
//! actual delta dependencies axiom-free (2026-09-08, SHA256
//! c569cdea892b915b3b168b1508d5d399416b6d160f45f7ab00914d8da7f07145).
//! Pure head discriminators have their own registration method, so iota can
//! consume them without depending on any delta proof. Registered Clean and
//! independent whole-corpus replay checks remain integration obligations.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const PROOFS: &[(&str, &str)] = &[
    (
        r"def levelListEqSem_length (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) : Eq Nat (level_list_len us) (level_list_len vs) :=
LevelListEqSem.rec
 (fun (xs : ListType Level) (ys : ListType Level) (_ : LevelListEqSem xs ys) => Eq Nat (level_list_len xs) (level_list_len ys))
 (Eq.refl Nat Nat.zero)
 (fun (u : Level) (v : Level) (xs : ListType Level) (ys : ListType Level)
  (_hu : levelEqSem u v) (_hs : LevelListEqSem xs ys)
  (ih : Eq Nat (level_list_len xs) (level_list_len ys)) =>
  Eq.cong Nat Nat Nat.succ (level_list_len xs) (level_list_len ys) ih) us vs h",
        "Related universe lists have the same actual length, proved by their two constructors.",
    ),
    (
        r"def levelListEqSem_list_getD (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) : forall (i : Nat), levelEqSem (list_getD us i) (list_getD vs i) :=
LevelListEqSem.rec
 (fun (xs : ListType Level) (ys : ListType Level) (_ : LevelListEqSem xs ys) => forall (i : Nat), levelEqSem (list_getD xs i) (list_getD ys i))
 (fun (_i : Nat) => levelEqSem_refl Level.zero)
 (fun (u : Level) (v : Level) (xs : ListType Level) (ys : ListType Level)
  (hu : levelEqSem u v) (_hs : LevelListEqSem xs ys)
  (ih : forall (i : Nat), levelEqSem (list_getD xs i) (list_getD ys i)) =>
  fun (i : Nat) => Nat.rec
   (fun (j : Nat) => levelEqSem (list_getD (ListType.cons Level u xs) j) (list_getD (ListType.cons Level v ys) j))
   hu
   (fun (j : Nat) (_ : levelEqSem (list_getD (ListType.cons Level u xs) j) (list_getD (ListType.cons Level v ys) j)) => ih j)
   i) us vs h",
        "Same-position lookup returns semantically equal levels, including zero defaults beyond either equally long list.",
    ),
    (
        r"def paramSubstN_semantic_values (ps : ListType Name) (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) (n : Name) : levelEqSem (paramSubstN ps us n) (paramSubstN ps vs n) :=
OptionType.rec Nat
 (fun (found : OptionType Nat) => levelEqSem
  (OptionType.rec Nat (fun (_ : OptionType Nat) => Level) (Level.param n) (fun (i : Nat) => list_getD us i) found)
  (OptionType.rec Nat (fun (_ : OptionType Nat) => Level) (Level.param n) (fun (i : Nat) => list_getD vs i) found))
 (levelEqSem_refl (Level.param n))
 (fun (i : Nat) => levelListEqSem_list_getD us vs h i)
 (nameIdx ps n)",
        "Pointwise semantic agreement for one identical ordered parameter list and related value lists. Neither NoDup nor parameter/value arity is required.",
    ),
    (
        r"def substL_pointwise_semantic (s : Name -> Level) (t : Name -> Level) (h : forall (n : Name), levelEqSem (s n) (t n)) (l : Level) : levelEqSem (substL s l) (substL t l) :=
Level.rec
 (fun (l0 : Level) => levelEqSem (substL s l0) (substL t l0))
 (levelEqSem_refl Level.zero)
 (fun (u : Level) (ih : levelEqSem (substL s u) (substL t u)) =>
  fun (r : Name -> Nat) => Eq.cong Nat Nat Nat.succ (evalL r (substL s u)) (evalL r (substL t u)) (ih r))
 (fun (u : Level) (v : Level) (ihu : levelEqSem (substL s u) (substL t u)) (ihv : levelEqSem (substL s v) (substL t v)) =>
  fun (r : Name -> Nat) => universe_bridge_congr2 Nat Nat Nat natMax
   (evalL r (substL s u)) (evalL r (substL t u)) (evalL r (substL s v)) (evalL r (substL t v)) (ihu r) (ihv r))
 (fun (u : Level) (v : Level) (ihu : levelEqSem (substL s u) (substL t u)) (ihv : levelEqSem (substL s v) (substL t v)) =>
  fun (r : Name -> Nat) => universe_bridge_congr2 Nat Nat Nat imaxNat
   (evalL r (substL s u)) (evalL r (substL t u)) (evalL r (substL s v)) (evalL r (substL t v)) (ihu r) (ihv r))
 (fun (n : Name) => h n) l",
        "Pointwise semantically equivalent substitutions give semantically equal results on the same raw level, including max and imax. No function-extensionality axiom.",
    ),
    (
        r"def mapLL_substL_pointwise_semantic (s : Name -> Level) (t : Name -> Level) (h : forall (n : Name), levelEqSem (s n) (t n)) (us : ListType Level) : LevelListEqSem (mapLL (substL s) us) (mapLL (substL t) us) :=
ListType.rec Level
 (fun (xs : ListType Level) => LevelListEqSem (mapLL (substL s) xs) (mapLL (substL t) xs))
 LevelListEqSem.nil
 (fun (u : Level) (xs : ListType Level)
  (ih : LevelListEqSem (mapLL (substL s) xs) (mapLL (substL t) xs)) =>
  LevelListEqSem.cons (substL s u) (substL t u)
   (mapLL (substL s) xs) (mapLL (substL t) xs) (substL_pointwise_semantic s t h u) ih) us",
        "Map the same universe-argument list with pointwise equivalent substitutions.",
    ),
    (
        r"def instL_pointwise_semantic (s : Name -> Level) (t : Name -> Level) (h : forall (n : Name), levelEqSem (s n) (t n)) (e : KExpr) : KExprUniverseEq (instL s e) (instL t e) :=
KExpr.rec
 (fun (e0 : KExpr) => KExprUniverseEq (instL s e0) (instL t e0))
 (fun (u : Level) => KExprUniverseEq.sort (substL s u) (substL t u) (substL_pointwise_semantic s t h u))
 (fun (i : Nat) => KExprUniverseEq.bvar i)
 (fun (f : KExpr) (a : KExpr) (ihf : KExprUniverseEq (instL s f) (instL t f)) (iha : KExprUniverseEq (instL s a) (instL t a)) =>
  KExprUniverseEq.app (instL s f) (instL t f) (instL s a) (instL t a) ihf iha)
 (fun (A : KExpr) (b : KExpr) (ihA : KExprUniverseEq (instL s A) (instL t A)) (ihb : KExprUniverseEq (instL s b) (instL t b)) =>
  KExprUniverseEq.lam (instL s A) (instL t A) (instL s b) (instL t b) ihA ihb)
 (fun (A : KExpr) (B : KExpr) (ihA : KExprUniverseEq (instL s A) (instL t A)) (ihB : KExprUniverseEq (instL s B) (instL t B)) =>
  KExprUniverseEq.pi (instL s A) (instL t A) (instL s B) (instL t B) ihA ihB)
 (fun (n : Name) (us : ListType Level) =>
  KExprUniverseEq.const n (mapLL (substL s) us) (mapLL (substL t) us) (mapLL_substL_pointwise_semantic s t h us))
 (fun (A : KExpr) (v : KExpr) (b : KExpr)
  (ihA : KExprUniverseEq (instL s A) (instL t A))
  (ihv : KExprUniverseEq (instL s v) (instL t v))
  (ihb : KExprUniverseEq (instL s b) (instL t b)) =>
  KExprUniverseEq.let_ (instL s A) (instL t A) (instL s v) (instL t v) (instL s b) (instL t b) ihA ihv ihb)
 (fun (n : Name) (i : Nat) (sub : KExpr) (ih : KExprUniverseEq (instL s sub) (instL t sub)) =>
  KExprUniverseEq.proj n i (instL s sub) (instL t sub) ih)
 (fun (n : Nat) => KExprUniverseEq.lit n) e",
        "All nine raw expression constructors preserve same-body semantic substitution. Loose BVars and undeclared universe parameters are allowed; no typing/support premise.",
    ),
    (
        r"def instLevels_semantic_values (ps : ListType Name) (body : KExpr) (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) : KExprUniverseEq (instLevels ps body us) (instLevels ps body vs) :=
instL_pointwise_semantic (paramSubstN ps us) (paramSubstN ps vs) (paramSubstN_semantic_values ps us vs h) body",
        "The identical schematic body instantiated with one identical ordered parameter list and related level lists is structurally universe-equivalent. No NoDup, body support, closedness or exact-arity assumption.",
    ),
    (
        r"def kdef_value_at_semantic_values (env : DefEnv) (n : Name) (us : ListType Level) (vs : ListType Level) (A : KExpr)
 (get : Eq (OptionType KExpr) (kdef_value_at env n us) (OptionType.some KExpr A))
 (related : LevelListEqSem us vs) (C : Type)
 (k : forall (B : KExpr), Eq (OptionType KExpr) (kdef_value_at env n vs) (OptionType.some KExpr B) -> KExprUniverseEq A B -> C) : C :=
kdef_value_at_some_inv env n us A get C
 (fun (defn : KDefSig)
  (found : Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig defn))
  (arity : kconst_arity (kdef_signature defn) us)
  (result : Eq KExpr A (kdef_inst_value defn us)) =>
  k (kdef_inst_value defn vs)
   (kdef_value_at_intro env n defn vs found
    (Eq.trans Nat (name_list_len (kconst_params (kdef_signature defn))) (level_list_len us) (level_list_len vs)
     arity (levelListEqSem_length us vs related)))
   (Eq.substType KExpr (fun (X : KExpr) => KExprUniverseEq X (kdef_inst_value defn vs))
    (kdef_inst_value defn us) A (Eq.symm KExpr A (kdef_inst_value defn us) result)
    (instLevels_semantic_values (kconst_params (kdef_signature defn)) (kdef_value defn) us vs related)))",
        "Derive the second successful guarded value lookup and semantic output relation from the original lookup and related universes, using actual inversion, preserved arity and introduction. No assumed output lookup, step, typing, NoDup or body support.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def semantic_delta_params : ListType Name := ListType.cons Name Name.anonymous (ListType.nil Name)",
        "Single shared parameter list for the guarded lookup controls.",
    ),
    (
        r"def semantic_delta_one : Level := Level.succ Level.zero",
        "Concrete nonzero universe.",
    ),
    (
        r"def semantic_delta_raw_one : Level := Level.imax semantic_delta_one semantic_delta_one",
        "Raw syntax distinct from one, but equal under every universe valuation.",
    ),
    (
        r"def semantic_delta_us_raw : ListType Level := ListType.cons Level semantic_delta_raw_one (ListType.nil Level)",
        "Source universe arguments for the semantic replacement control.",
    ),
    (
        r"def semantic_delta_us_one : ListType Level := ListType.cons Level semantic_delta_one (ListType.nil Level)",
        "Target universe arguments for the nonzero lookup control.",
    ),
    (
        r"def semantic_delta_sig : KDefSig := KDefSig.mk (KConstSig.mk semantic_delta_params (KExpr.sort (Level.succ (Level.param Name.anonymous)))) (KExpr.sort (Level.param Name.anonymous))",
        "One stored signature and body share their actual ordered parameter list; this fixture does not assert production admission.",
    ),
    (
        r"def semantic_delta_env : DefEnv := DefEnv.addDef DefEnv.empty Name.anonymous semantic_delta_sig",
        "Concrete one-definition environment, not a postulated lookup function.",
    ),
    (
        r"def semantic_delta_universes_related : LevelListEqSem semantic_delta_us_raw semantic_delta_us_one :=
LevelListEqSem.cons semantic_delta_raw_one semantic_delta_one (ListType.nil Level) (ListType.nil Level)
 (fun (_r : Name -> Nat) => Eq.refl Nat (Nat.succ Nat.zero)) LevelListEqSem.nil",
        "Nontrivial pointwise semantic equality, raw imax(1,1) versus one.",
    ),
    (
        r"def semantic_delta_lookup_at (u : Level) : Eq (OptionType KExpr)
 (kdef_value_at semantic_delta_env Name.anonymous (ListType.cons Level u (ListType.nil Level)))
 (OptionType.some KExpr (KExpr.sort u)) :=
kdef_value_at_intro semantic_delta_env Name.anonymous semantic_delta_sig (ListType.cons Level u (ListType.nil Level))
 (Eq.refl (OptionType KDefSig) (OptionType.some KDefSig semantic_delta_sig))
 (Eq.refl Nat (Nat.succ Nat.zero))",
        "Actual generic guarded lookup introduced from a concrete stored record and exact arity.",
    ),
    (
        r"def semantic_delta_lookup_zero : Eq (OptionType KExpr) (kdef_value_at semantic_delta_env Name.anonymous (ListType.cons Level Level.zero (ListType.nil Level))) (OptionType.some KExpr (KExpr.sort Level.zero)) := semantic_delta_lookup_at Level.zero",
        "Concrete zero-universe successful lookup.",
    ),
    (
        r"def semantic_delta_lookup_one : Eq (OptionType KExpr) (kdef_value_at semantic_delta_env Name.anonymous semantic_delta_us_one) (OptionType.some KExpr (KExpr.sort semantic_delta_one)) := semantic_delta_lookup_at semantic_delta_one",
        "Concrete nonzero-universe successful lookup.",
    ),
    (
        r"def semantic_delta_compat_nonzero : KExprUniverseEq (KExpr.sort semantic_delta_raw_one) (KExpr.sort semantic_delta_one) :=
kdef_value_at_semantic_values semantic_delta_env Name.anonymous semantic_delta_us_raw semantic_delta_us_one
 (KExpr.sort semantic_delta_raw_one) (semantic_delta_lookup_at semantic_delta_raw_one)
 semantic_delta_universes_related (KExprUniverseEq (KExpr.sort semantic_delta_raw_one) (KExpr.sort semantic_delta_one))
 (fun (B : KExpr)
  (get : Eq (OptionType KExpr) (kdef_value_at semantic_delta_env Name.anonymous semantic_delta_us_one) (OptionType.some KExpr B))
  (related : KExprUniverseEq (KExpr.sort semantic_delta_raw_one) B) =>
  Eq.substType KExpr (fun (X : KExpr) => KExprUniverseEq (KExpr.sort semantic_delta_raw_one) X)
   B (KExpr.sort semantic_delta_one)
   (option_some_inj KExpr B (KExpr.sort semantic_delta_one)
    (Eq.trans (OptionType KExpr) (OptionType.some KExpr B)
     (kdef_value_at semantic_delta_env Name.anonymous semantic_delta_us_one)
     (OptionType.some KExpr (KExpr.sort semantic_delta_one))
     (Eq.symm (OptionType KExpr) (kdef_value_at semantic_delta_env Name.anonymous semantic_delta_us_one) (OptionType.some KExpr B) get)
     semantic_delta_lookup_one)) related)",
        "The actual CPS compatibility proof is executed on a nonzero semantic change. Both its returned graph equation and semantic relation are consumed to identify the result.",
    ),
    (
        r"def semantic_delta_missing_name : Eq (OptionType KExpr) (kdef_value_at semantic_delta_env (Name.str Name.anonymous Nat.zero) semantic_delta_us_one) (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
        "Actual missing-name lookup stays refused at nonzero universes.",
    ),
    (
        r"def semantic_delta_wrong_arity : Eq (OptionType KExpr) (kdef_value_at semantic_delta_env Name.anonymous (ListType.nil Level)) (OptionType.none KExpr) := Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
        "An existing body with a missing universe argument is refused; semantic replacement never bypasses the arity guard.",
    ),
    (
        r"def semantic_delta_no_body_support : KExprUniverseEq
 (instLevels (ListType.nil Name) (KExpr.sort (Level.param Name.anonymous)) semantic_delta_us_raw)
 (instLevels (ListType.nil Name) (KExpr.sort (Level.param Name.anonymous)) semantic_delta_us_one) :=
instLevels_semantic_values (ListType.nil Name) (KExpr.sort (Level.param Name.anonymous))
 semantic_delta_us_raw semantic_delta_us_one semantic_delta_universes_related",
        "The raw same-body lemma allows an undeclared parameter and mismatched parameter/value arity. This is deliberately not a successful guarded lookup or a fixed-environment substitution-commutation claim.",
    ),
    (
        r"def semantic_delta_duplicate_params : KExprUniverseEq (KExpr.sort semantic_delta_raw_one) (KExpr.sort semantic_delta_one) :=
instLevels_semantic_values
 (ListType.cons Name Name.anonymous (ListType.cons Name Name.anonymous (ListType.nil Name)))
 (KExpr.sort (Level.param Name.anonymous))
 (ListType.cons Level semantic_delta_raw_one (ListType.cons Level Level.zero (ListType.nil Level)))
 (ListType.cons Level semantic_delta_one (ListType.cons Level Level.zero (ListType.nil Level)))
 (LevelListEqSem.cons semantic_delta_raw_one semantic_delta_one
  (ListType.cons Level Level.zero (ListType.nil Level)) (ListType.cons Level Level.zero (ListType.nil Level))
  (fun (_r : Name -> Nat) => Eq.refl Nat (Nat.succ Nat.zero))
  (LevelListEqSem.cons Level.zero Level.zero (ListType.nil Level) (ListType.nil Level)
   (levelEqSem_refl Level.zero) LevelListEqSem.nil))",
        "The same duplicate parameter list selects the same first position on both sides. No NoDup is needed for this model relation; this does not identify Rust's first-match and last-match paths.",
    ),
];

const HEAD_VIEW_PROOFS: &[(&str, &str)] = &[
    (
        r"def kexprUniverseEq_const_name (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 Eq (OptionType Name) (kexpr_const_name e) (kexpr_const_name e2) :=
 KExprUniverseEq.rec
 (fun (a : KExpr) (b : KExpr) (_h : KExprUniverseEq a b) => Eq (OptionType Name) (kexpr_const_name a) (kexpr_const_name b))
 (fun (u : Level) (v : Level) (hu : levelEqSem u v) => Eq.refl (OptionType Name) (OptionType.none Name))
 (fun (i : Nat) => Eq.refl (OptionType Name) (OptionType.none Name))
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (_ih0 : Eq (OptionType Name) (kexpr_const_name f) (kexpr_const_name f2)) (_ih1 : Eq (OptionType Name) (kexpr_const_name a) (kexpr_const_name a2)) => Eq.refl (OptionType Name) (OptionType.none Name))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (_ih0 : Eq (OptionType Name) (kexpr_const_name A) (kexpr_const_name A2)) (_ih1 : Eq (OptionType Name) (kexpr_const_name b) (kexpr_const_name b2)) => Eq.refl (OptionType Name) (OptionType.none Name))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (_ih0 : Eq (OptionType Name) (kexpr_const_name A) (kexpr_const_name A2)) (_ih1 : Eq (OptionType Name) (kexpr_const_name b) (kexpr_const_name b2)) => Eq.refl (OptionType Name) (OptionType.none Name))
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (hus : LevelListEqSem us vs) => Eq.refl (OptionType Name) (OptionType.some Name n))
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (_ih0 : Eq (OptionType Name) (kexpr_const_name A) (kexpr_const_name A2)) (_ih1 : Eq (OptionType Name) (kexpr_const_name v) (kexpr_const_name v2)) (_ih2 : Eq (OptionType Name) (kexpr_const_name b) (kexpr_const_name b2)) => Eq.refl (OptionType Name) (OptionType.none Name))
 (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : KExprUniverseEq sub sub2) (_ih0 : Eq (OptionType Name) (kexpr_const_name sub) (kexpr_const_name sub2)) => Eq.refl (OptionType Name) (OptionType.none Name))
 (fun (n : Nat) => Eq.refl (OptionType Name) (OptionType.none Name)) e e2 h",
        "The actual constant-name view preserves the exact name under semantic universe replacement; every nonconstant constructor maps to none.",
    ),
    (
        r"def kexprUniverseEq_const_levels (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 LevelListEqSem (kexpr_const_levels e) (kexpr_const_levels e2) :=
 KExprUniverseEq.rec
 (fun (a : KExpr) (b : KExpr) (_h : KExprUniverseEq a b) => LevelListEqSem (kexpr_const_levels a) (kexpr_const_levels b))
 (fun (u : Level) (v : Level) (hu : levelEqSem u v) => LevelListEqSem.nil)
 (fun (i : Nat) => LevelListEqSem.nil)
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (_ih0 : LevelListEqSem (kexpr_const_levels f) (kexpr_const_levels f2)) (_ih1 : LevelListEqSem (kexpr_const_levels a) (kexpr_const_levels a2)) => LevelListEqSem.nil)
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (_ih0 : LevelListEqSem (kexpr_const_levels A) (kexpr_const_levels A2)) (_ih1 : LevelListEqSem (kexpr_const_levels b) (kexpr_const_levels b2)) => LevelListEqSem.nil)
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (_ih0 : LevelListEqSem (kexpr_const_levels A) (kexpr_const_levels A2)) (_ih1 : LevelListEqSem (kexpr_const_levels b) (kexpr_const_levels b2)) => LevelListEqSem.nil)
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (hus : LevelListEqSem us vs) => hus)
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (_ih0 : LevelListEqSem (kexpr_const_levels A) (kexpr_const_levels A2)) (_ih1 : LevelListEqSem (kexpr_const_levels v) (kexpr_const_levels v2)) (_ih2 : LevelListEqSem (kexpr_const_levels b) (kexpr_const_levels b2)) => LevelListEqSem.nil)
 (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : KExprUniverseEq sub sub2) (_ih0 : LevelListEqSem (kexpr_const_levels sub) (kexpr_const_levels sub2)) => LevelListEqSem.nil)
 (fun (n : Nat) => LevelListEqSem.nil) e e2 h",
        "The actual constant-level view returns related supplied levels; all nonconstant constructors share its nil default.",
    ),
];

const REDUCT_PROOFS: &[(&str, &str)] = &[
    (
        r"def delta_reduct_of_value_some (env : DefEnv) (e : KExpr) (n : Name) (value : KExpr)
 (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n))
 (found : Eq (OptionType KExpr) (kdef_value_at env n (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr value)) :
 Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr (apply_spine (kapp_args e) value)) :=
 opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn e))
  (fun (nm : Name) => opt_bind KExpr KExpr (kdef_value_at env nm (kexpr_const_levels (kapp_fn e)))
    (fun (body : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) body)))
  n (apply_spine (kapp_args e) value) head
  (opt_bind_some_intro KExpr KExpr (kdef_value_at env n (kexpr_const_levels (kapp_fn e)))
    (fun (body : KExpr) => OptionType.some KExpr (apply_spine (kapp_args e) body))
    value (apply_spine (kapp_args e) value) found
    (Eq.refl (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) value))))",
        "Reconstruct the actual delta evaluator from a successful constant view and guarded instantiated body lookup, without a step assumption.",
    ),
    (
        r"def delta_reduct_semantic_compat (env : DefEnv) (e : KExpr) (e2 : KExpr)
 (related : KExprUniverseEq e e2) (r : KExpr)
 (get : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr r)) (C : Type)
 (k : forall (r2 : KExpr),
   Eq (OptionType KExpr) (delta_reduct env e2) (OptionType.some KExpr r2) ->
   KExprUniverseEq r r2 -> C) : C :=
 delta_reduct_some_inv_type env e r C get
  (fun (n : Name) (value : KExpr)
    (head : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n))
    (found : Eq (OptionType KExpr) (kdef_value_at env n (kexpr_const_levels (kapp_fn e))) (OptionType.some KExpr value))
    (result : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) value)) (OptionType.some KExpr r)) =>
    kdef_value_at_semantic_values env n (kexpr_const_levels (kapp_fn e)) (kexpr_const_levels (kapp_fn e2))
      value found
      (kexprUniverseEq_const_levels (kapp_fn e) (kapp_fn e2) (kexprUniverseEq_kapp_fn e e2 related)) C
      (fun (value2 : KExpr)
        (found2 : Eq (OptionType KExpr) (kdef_value_at env n (kexpr_const_levels (kapp_fn e2))) (OptionType.some KExpr value2))
        (values : KExprUniverseEq value value2) =>
        k (apply_spine (kapp_args e2) value2)
          (delta_reduct_of_value_some env e2 n value2
            (Eq.trans (OptionType Name)
              (kexpr_const_name (kapp_fn e2)) (kexpr_const_name (kapp_fn e)) (OptionType.some Name n)
              (Eq.symm (OptionType Name)
                (kexpr_const_name (kapp_fn e)) (kexpr_const_name (kapp_fn e2))
                (kexprUniverseEq_const_name (kapp_fn e) (kapp_fn e2) (kexprUniverseEq_kapp_fn e e2 related))) head)
            found2)
          (Eq.substType KExpr (fun (x : KExpr) => KExprUniverseEq x (apply_spine (kapp_args e2) value2))
            (apply_spine (kapp_args e) value) r
            (option_some_inj KExpr (apply_spine (kapp_args e) value) r result)
            (kexprUniverseEq_apply_spine (kapp_args e) (kapp_args e2)
              (kexprUniverseEq_kapp_args e e2 related) value value2 values))))",
        "Actual expression-level delta simulation under semantic universe replacement in one fixed environment: the target reduct and graph equality are derived by inversion, arity-preserving lookup and spine reconstruction, not assumed.",
    ),
];

const REDUCT_CONTROLS: &[(&str, &str)] = &[
    (
        r"def semantic_delta_spine_input (u : Level) : KExpr :=
 KExpr.app
  (KExpr.app (KExpr.const Name.anonymous (ListType.cons Level u (ListType.nil Level))) (KExpr.sort u))
  (KExpr.lit Nat.zero)",
        "A genuine two-argument application spine whose head and first argument both carry universes.",
    ),
    (
        r"def semantic_delta_spine_output (u : Level) : KExpr :=
 KExpr.app (KExpr.app (KExpr.sort u) (KExpr.sort u)) (KExpr.lit Nat.zero)",
        "The actual instantiated schematic body with both original arguments re-applied in order.",
    ),
    (
        r"def semantic_delta_spine_step_at (u : Level) :
 Eq (OptionType KExpr) (delta_reduct semantic_delta_env (semantic_delta_spine_input u))
   (OptionType.some KExpr (semantic_delta_spine_output u)) :=
 delta_reduct_of_value_some semantic_delta_env (semantic_delta_spine_input u) Name.anonymous (KExpr.sort u)
  (Eq.refl (OptionType Name) (OptionType.some Name Name.anonymous))
  (semantic_delta_lookup_at u)",
        "The real delta computation succeeds on the two-argument spine at any supplied universe, using its one-parameter signature.",
    ),
    (
        r"def semantic_delta_spine_related :
 KExprUniverseEq (semantic_delta_spine_input semantic_delta_raw_one) (semantic_delta_spine_input semantic_delta_one) :=
 KExprUniverseEq.app
  (KExpr.app (KExpr.const Name.anonymous semantic_delta_us_raw) (KExpr.sort semantic_delta_raw_one))
  (KExpr.app (KExpr.const Name.anonymous semantic_delta_us_one) (KExpr.sort semantic_delta_one))
  (KExpr.lit Nat.zero) (KExpr.lit Nat.zero)
  (KExprUniverseEq.app
    (KExpr.const Name.anonymous semantic_delta_us_raw) (KExpr.const Name.anonymous semantic_delta_us_one)
    (KExpr.sort semantic_delta_raw_one) (KExpr.sort semantic_delta_one)
    (KExprUniverseEq.const Name.anonymous semantic_delta_us_raw semantic_delta_us_one semantic_delta_universes_related)
    (KExprUniverseEq.sort semantic_delta_raw_one semantic_delta_one
      (fun (_rho : Name -> Nat) => Eq.refl Nat (Nat.succ Nat.zero))))
  (KExprUniverseEq.lit Nat.zero)",
        "Non-syntactically-identical but semantically related head universe lists and first arguments; the second literal payload is fixed.",
    ),
    (
        r"def semantic_delta_spine_caller :
 KExprUniverseEq (semantic_delta_spine_output semantic_delta_raw_one) (semantic_delta_spine_output semantic_delta_one) :=
 delta_reduct_semantic_compat semantic_delta_env
  (semantic_delta_spine_input semantic_delta_raw_one) (semantic_delta_spine_input semantic_delta_one)
  semantic_delta_spine_related (semantic_delta_spine_output semantic_delta_raw_one)
  (semantic_delta_spine_step_at semantic_delta_raw_one)
  (KExprUniverseEq (semantic_delta_spine_output semantic_delta_raw_one) (semantic_delta_spine_output semantic_delta_one))
  (fun (r2 : KExpr)
    (get2 : Eq (OptionType KExpr) (delta_reduct semantic_delta_env (semantic_delta_spine_input semantic_delta_one)) (OptionType.some KExpr r2))
    (related : KExprUniverseEq (semantic_delta_spine_output semantic_delta_raw_one) r2) =>
    Eq.substType KExpr
      (fun (x : KExpr) => KExprUniverseEq (semantic_delta_spine_output semantic_delta_raw_one) x)
      r2 (semantic_delta_spine_output semantic_delta_one)
      (option_some_inj KExpr r2 (semantic_delta_spine_output semantic_delta_one)
        (Eq.trans (OptionType KExpr)
          (OptionType.some KExpr r2) (delta_reduct semantic_delta_env (semantic_delta_spine_input semantic_delta_one))
          (OptionType.some KExpr (semantic_delta_spine_output semantic_delta_one))
          (Eq.symm (OptionType KExpr)
            (delta_reduct semantic_delta_env (semantic_delta_spine_input semantic_delta_one)) (OptionType.some KExpr r2) get2)
          (semantic_delta_spine_step_at semantic_delta_one)))
      related)",
        "Actual nonzero two-argument caller of the delta CPS theorem. Consumes both its derived graph equation and related output, checking the result against the independently reconstructed target computation.",
    ),
    (
        r"def semantic_delta_spine_wrong_arity :
 Eq (OptionType KExpr)
  (delta_reduct semantic_delta_env
    (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort semantic_delta_one)))
  (OptionType.none KExpr) :=
 Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
        "An application argument does not supply a missing universe argument: actual delta remains blocked by signature arity.",
    ),
    (
        r"def semantic_delta_spine_missing_name :
 Eq (OptionType KExpr)
  (delta_reduct semantic_delta_env
    (KExpr.app (KExpr.const (Name.str Name.anonymous Nat.zero) semantic_delta_us_one) (KExpr.sort semantic_delta_one)))
  (OptionType.none KExpr) :=
 Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
        "A related-universe application cannot manufacture a definition at an absent head name.",
    ),
];

impl Specification {
    /// Pure constant views, registerable before either delta or iota callers.
    /// Requires KExprUniverseEq and the existing computational const views.
    pub(super) fn add_semantic_head_discriminators(&mut self) -> Result<(), SpecError> {
        for (source, description) in HEAD_VIEW_PROOFS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }

    /// Requires the head discriminators, guarded semantic lookup, the actual
    /// Type-valued option inverter/introducer, and semantic spine compatibility.
    /// Derives the replacement delta computation, without an output-step premise.
    pub(super) fn add_semantic_delta_reduct_compat(&mut self) -> Result<(), SpecError> {
        for (source, description) in REDUCT_PROOFS.iter().chain(REDUCT_CONTROLS) {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }

    /// Requires the semantic universe relations and the genuine delta
    /// signature-lookup inverter/introducer; no acceptance or confluence stage.
    pub(super) fn add_semantic_delta_compat(&mut self) -> Result<(), SpecError> {
        for (source, description) in PROOFS.iter().chain(CONTROLS) {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn semantic_delta_reduct_and_spine_controls_are_kernel_checked() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "kexprUniverseEq_const_name",
            "kexprUniverseEq_const_levels",
            "delta_reduct_some_inv_type",
            "delta_reduct_of_value_some",
            "delta_reduct_semantic_compat",
            "semantic_delta_spine_step_at",
            "semantic_delta_spine_related",
            "semantic_delta_spine_caller",
            "semantic_delta_spine_wrong_arity",
            "semantic_delta_spine_missing_name",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered checked delta declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }

    #[test]
    fn semantic_delta_spine_cannot_bypass_universe_arity() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = crate::test_utils::build_spec_with_stack();
            assert!(spec.add_recursive_def(
                "def semantic_delta_forged_spine_arity : Eq (OptionType KExpr) (delta_reduct semantic_delta_env (KExpr.app (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort semantic_delta_one))) (OptionType.some KExpr (KExpr.app (KExpr.sort semantic_delta_one) (KExpr.sort semantic_delta_one))) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.sort semantic_delta_one) (KExpr.sort semantic_delta_one)))",
                "Rejected control: an expression argument cannot discharge the missing universe-arity guard."
            ).is_err());
        });
    }

    #[test]
    fn semantic_delta_lookup_compatibility_and_controls_are_kernel_checked() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "levelListEqSem_length",
            "levelListEqSem_list_getD",
            "paramSubstN_semantic_values",
            "substL_pointwise_semantic",
            "mapLL_substL_pointwise_semantic",
            "instL_pointwise_semantic",
            "instLevels_semantic_values",
            "kdef_value_at_semantic_values",
            "semantic_delta_universes_related",
            "semantic_delta_lookup_at",
            "semantic_delta_lookup_zero",
            "semantic_delta_lookup_one",
            "semantic_delta_compat_nonzero",
            "semantic_delta_missing_name",
            "semantic_delta_wrong_arity",
            "semantic_delta_no_body_support",
            "semantic_delta_duplicate_params",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered checked declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }
}

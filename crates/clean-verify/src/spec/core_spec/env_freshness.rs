// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructor-ID-aware freshness in the actual new-declaration extension model.
//! The canonical KEnv fold and WellFormedCtorDecls guard are defined in
//! env_extensions.rs. These proofs expose their obligations and consume them
//! through InductiveExtension, EnvSound and KernelAddDeclAccepts. This is not a
//! proof of Rust admission, auxiliary-name generation, or its names-present
//! idempotent no-op path. Existing typing-fragment limits remain unchanged.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const DATA: &[&str] = &[
    r"def env_freshness_one : Nat := Nat.succ Nat.zero",
    r"def env_freshness_two : Nat := Nat.succ env_freshness_one",
    r"def env_freshness_three : Nat := Nat.succ env_freshness_two",
    r"def env_freshness_type : KExpr := KExpr.sort (Level.succ Level.zero)",
    r"def env_freshness_ctors (id : Nat) : CtorDecls := CtorDecls.cons (CtorDecl.mk id (KExpr.bvar Nat.zero)) CtorDecls.nil",
    r"def env_freshness_first : KEnv := KEnv.addInductive KEnv.empty Nat.zero Nat.zero env_freshness_type (env_freshness_ctors env_freshness_one)",
    r"def env_freshness_second : KEnv := KEnv.addInductive env_freshness_first env_freshness_two Nat.zero env_freshness_type (env_freshness_ctors env_freshness_three)",
    r"def env_freshness_const_result : KEnv := KEnv.addConst env_freshness_first ConstExtensionKind.reducible_ env_freshness_two env_freshness_type (KExpr.sort Level.zero)",
];

const PROOFS: &[(&str, &str, &str)] = &[
    (
        "env_freshness_and_intro",
        r"forall (a : Bool) (b : Bool), @Eq Bool a Bool.true -> @Eq Bool b Bool.true -> @Eq Bool (Bool.and a b) Bool.true",
        r"fun (a : Bool) (b : Bool) (ha : @Eq Bool a Bool.true) (hb : @Eq Bool b Bool.true) =>
@Eq.trans Bool (Bool.and a b) b Bool.true
 (@Eq.cong Bool Bool (fun (x : Bool) => Bool.and x b) a Bool.true ha) hb",
    ),
    (
        "env_freshness_and_false_right",
        r"forall (a : Bool), @Eq Bool (Bool.and a Bool.false) Bool.false",
        r"fun (a : Bool) => @Bool.rec
 (fun (x : Bool) => @Eq Bool (Bool.and x Bool.false) Bool.false)
 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.false) a",
    ),
    (
        "ctor_ids_fresh_head_refused",
        r"forall (id : Nat) (ty : KExpr) (rest : CtorDecls),
@Eq Bool (ctor_ids_fresh_b (CtorDecls.cons (CtorDecl.mk id ty) rest) id) Bool.false",
        r"fun (id : Nat) (ty : KExpr) (rest : CtorDecls) =>
@Eq.cong Bool Bool (fun (b : Bool) => Bool.and (Bool.not b) (ctor_ids_fresh_b rest id))
 (nat_eqb id id) Bool.true (nat_eqb_refl id)",
    ),
    (
        "ctor_ids_fresh_tail_refused",
        r"forall (c : CtorDecl) (rest : CtorDecls) (id : Nat),
@Eq Bool (ctor_ids_fresh_b rest id) Bool.false ->
@Eq Bool (ctor_ids_fresh_b (CtorDecls.cons c rest) id) Bool.false",
        r"fun (c : CtorDecl) (rest : CtorDecls) (id : Nat)
 (h : @Eq Bool (ctor_ids_fresh_b rest id) Bool.false) =>
@Eq.trans Bool (ctor_ids_fresh_b (CtorDecls.cons c rest) id)
 (Bool.and (Bool.not (nat_eqb (ctor_decl_id c) id)) Bool.false) Bool.false
 (@Eq.cong Bool Bool (fun (b : Bool) => Bool.and (Bool.not (nat_eqb (ctor_decl_id c) id)) b)
   (ctor_ids_fresh_b rest id) Bool.false h)
 (env_freshness_and_false_right (Bool.not (nat_eqb (ctor_decl_id c) id)))",
    ),
    (
        "kenv_stored_ctor_refused",
        r"forall (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls) (id : Nat),
@Eq Bool (ctor_ids_fresh_b ctors id) Bool.false ->
@Eq Bool (kenv_fresh (KEnv.addInductive env family np ty ctors) id) Bool.false",
        r"fun (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls) (id : Nat)
 (h : @Eq Bool (ctor_ids_fresh_b ctors id) Bool.false) =>
@Eq.trans Bool (kenv_fresh (KEnv.addInductive env family np ty ctors) id)
 (Bool.and (Bool.not (nat_eqb family id)) Bool.false) Bool.false
 (@Eq.cong Bool Bool
   (fun (b : Bool) => Bool.and (Bool.not (nat_eqb family id)) (Bool.and b (kenv_fresh env id)))
   (ctor_ids_fresh_b ctors id) Bool.false h)
 (env_freshness_and_false_right (Bool.not (nat_eqb family id)))",
    ),
    (
        "kenv_occupied_const_preserved",
        r"forall (env : KEnv) (kind : ConstExtensionKind) (n : Nat) (ty : KExpr) (value : KExpr) (id : Nat),
@Eq Bool (kenv_fresh env id) Bool.false ->
@Eq Bool (kenv_fresh (KEnv.addConst env kind n ty value) id) Bool.false",
        r"fun (env : KEnv) (kind : ConstExtensionKind) (n : Nat) (ty : KExpr) (value : KExpr) (id : Nat)
 (h : @Eq Bool (kenv_fresh env id) Bool.false) =>
@Eq.trans Bool (kenv_fresh (KEnv.addConst env kind n ty value) id)
 (Bool.and (Bool.not (nat_eqb n id)) Bool.false) Bool.false
 (@Eq.cong Bool Bool (fun (b : Bool) => Bool.and (Bool.not (nat_eqb n id)) b)
   (kenv_fresh env id) Bool.false h)
 (env_freshness_and_false_right (Bool.not (nat_eqb n id)))",
    ),
    (
        "kenv_occupied_inductive_preserved",
        r"forall (env : KEnv) (n : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls) (id : Nat),
@Eq Bool (kenv_fresh env id) Bool.false ->
@Eq Bool (kenv_fresh (KEnv.addInductive env n np ty ctors) id) Bool.false",
        r"fun (env : KEnv) (n : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls) (id : Nat)
 (h : @Eq Bool (kenv_fresh env id) Bool.false) =>
@Eq.trans Bool (kenv_fresh (KEnv.addInductive env n np ty ctors) id)
 (Bool.and (Bool.not (nat_eqb n id)) (Bool.and (ctor_ids_fresh_b ctors id) Bool.false)) Bool.false
 (@Eq.cong Bool Bool (fun (b : Bool) => Bool.and (Bool.not (nat_eqb n id))
   (Bool.and (ctor_ids_fresh_b ctors id) b)) (kenv_fresh env id) Bool.false h)
 (@Eq.trans Bool (Bool.and (Bool.not (nat_eqb n id)) (Bool.and (ctor_ids_fresh_b ctors id) Bool.false))
   (Bool.and (Bool.not (nat_eqb n id)) Bool.false) Bool.false
   (@Eq.cong Bool Bool (fun (b : Bool) => Bool.and (Bool.not (nat_eqb n id)) b)
     (Bool.and (ctor_ids_fresh_b ctors id) Bool.false) Bool.false
     (env_freshness_and_false_right (ctor_ids_fresh_b ctors id)))
   (env_freshness_and_false_right (Bool.not (nat_eqb n id))))",
    ),
    (
        "fresh_ctor_decls_nil",
        r"forall (env : KEnv) (family : Nat), FreshCtorDecls env family CtorDecls.nil",
        r"fun (env : KEnv) (family : Nat) => @Eq.refl Bool Bool.true",
    ),
    (
        "fresh_ctor_decls_cons_intro",
        r"forall (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls),
FreshDeclName env (ctor_decl_id c) ->
@Eq Bool (Bool.not (nat_eqb family (ctor_decl_id c))) Bool.true ->
@Eq Bool (ctor_ids_fresh_b rest (ctor_decl_id c)) Bool.true ->
FreshCtorDecls env family rest -> FreshCtorDecls env family (CtorDecls.cons c rest)",
        r"fun (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls)
 (hf : FreshDeclName env (ctor_decl_id c))
 (hn : @Eq Bool (Bool.not (nat_eqb family (ctor_decl_id c))) Bool.true)
 (hd : @Eq Bool (ctor_ids_fresh_b rest (ctor_decl_id c)) Bool.true)
 (hr : FreshCtorDecls env family rest) =>
env_freshness_and_intro (kenv_fresh env (ctor_decl_id c))
 (Bool.and (Bool.not (nat_eqb family (ctor_decl_id c)))
   (Bool.and (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest))) hf
 (env_freshness_and_intro (Bool.not (nat_eqb family (ctor_decl_id c)))
   (Bool.and (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest)) hn
   (env_freshness_and_intro (ctor_ids_fresh_b rest (ctor_decl_id c))
     (ctor_decls_fresh_b env family rest) hd hr))",
    ),
    (
        "fresh_ctor_decls_head_old",
        r"forall (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls),
FreshCtorDecls env family (CtorDecls.cons c rest) -> FreshDeclName env (ctor_decl_id c)",
        r"fun (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls)
 (h : FreshCtorDecls env family (CtorDecls.cons c rest)) =>
band_eq_true_left (kenv_fresh env (ctor_decl_id c)) (Bool.and (Bool.not (nat_eqb family (ctor_decl_id c))) (Bool.and (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest))) h",
    ),
    (
        "fresh_ctor_decls_head_family",
        r"forall (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls),
FreshCtorDecls env family (CtorDecls.cons c rest) -> @Eq Bool (Bool.not (nat_eqb family (ctor_decl_id c))) Bool.true",
        r"fun (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls)
 (h : FreshCtorDecls env family (CtorDecls.cons c rest)) =>
band_eq_true_left (Bool.not (nat_eqb family (ctor_decl_id c))) (Bool.and (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest)) (band_eq_true_right (kenv_fresh env (ctor_decl_id c)) (Bool.and (Bool.not (nat_eqb family (ctor_decl_id c))) (Bool.and (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest))) h)",
    ),
    (
        "fresh_ctor_decls_head_distinct",
        r"forall (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls),
FreshCtorDecls env family (CtorDecls.cons c rest) -> @Eq Bool (ctor_ids_fresh_b rest (ctor_decl_id c)) Bool.true",
        r"fun (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls)
 (h : FreshCtorDecls env family (CtorDecls.cons c rest)) =>
band_eq_true_left (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest) (band_eq_true_right (Bool.not (nat_eqb family (ctor_decl_id c))) (Bool.and (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest)) (band_eq_true_right (kenv_fresh env (ctor_decl_id c)) (Bool.and (Bool.not (nat_eqb family (ctor_decl_id c))) (Bool.and (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest))) h))",
    ),
    (
        "fresh_ctor_decls_tail",
        r"forall (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls),
FreshCtorDecls env family (CtorDecls.cons c rest) -> FreshCtorDecls env family rest",
        r"fun (env : KEnv) (family : Nat) (c : CtorDecl) (rest : CtorDecls)
 (h : FreshCtorDecls env family (CtorDecls.cons c rest)) =>
band_eq_true_right (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest) (band_eq_true_right (Bool.not (nat_eqb family (ctor_decl_id c))) (Bool.and (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest)) (band_eq_true_right (kenv_fresh env (ctor_decl_id c)) (Bool.and (Bool.not (nat_eqb family (ctor_decl_id c))) (Bool.and (ctor_ids_fresh_b rest (ctor_decl_id c)) (ctor_decls_fresh_b env family rest))) h))",
    ),
    (
        "well_formed_ctor_decls_fresh",
        r"forall (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls),
WellFormedCtorDecls env family np ty ctors -> FreshCtorDecls env family ctors",
        r"fun (env : KEnv) (family : Nat) (np : Nat) (ty : KExpr) (ctors : CtorDecls)
 (h : WellFormedCtorDecls env family np ty ctors) =>
@WellFormedCtorDecls.rec env family np ty ctors
 (fun (_h : WellFormedCtorDecls env family np ty ctors) => FreshCtorDecls env family ctors)
 (fun (u : Level) (fresh : FreshCtorDecls env family ctors)
   (_result : @Eq KExpr (return_type ty) (KExpr.sort u))
   (_shape : @Eq Bool (ctor_decls_wf_b np ctors) Bool.true)
   (_typed : CtorsWellTyped u np ty ctors) => fresh) h",
    ),
    (
        "fresh_ctor_decls_occupied_refused",
        r"forall (env : KEnv) (family : Nat) (id : Nat) (ty : KExpr) (rest : CtorDecls) (C : Prop),
@Eq Bool (kenv_fresh env id) Bool.false ->
FreshCtorDecls env family (CtorDecls.cons (CtorDecl.mk id ty) rest) -> C",
        r"fun (env : KEnv) (family : Nat) (id : Nat) (ty : KExpr) (rest : CtorDecls) (C : Prop)
 (occupied : @Eq Bool (kenv_fresh env id) Bool.false)
 (fresh : FreshCtorDecls env family (CtorDecls.cons (CtorDecl.mk id ty) rest)) =>
bool_false_ne_true C (@Eq.trans Bool Bool.false (kenv_fresh env id) Bool.true
 (@Eq.symm Bool (kenv_fresh env id) Bool.false occupied)
 (fresh_ctor_decls_head_old env family (CtorDecl.mk id ty) rest fresh))",
    ),
    (
        "fresh_ctor_decls_self_refused",
        r"forall (env : KEnv) (id : Nat) (ty : KExpr) (rest : CtorDecls) (C : Prop),
FreshCtorDecls env id (CtorDecls.cons (CtorDecl.mk id ty) rest) -> C",
        r"fun (env : KEnv) (id : Nat) (ty : KExpr) (rest : CtorDecls) (C : Prop)
 (fresh : FreshCtorDecls env id (CtorDecls.cons (CtorDecl.mk id ty) rest)) =>
bool_false_ne_true C
 (@Eq.trans Bool Bool.false (Bool.not (nat_eqb id id)) Bool.true
   (@Eq.symm Bool (Bool.not (nat_eqb id id)) Bool.false
     (@Eq.cong Bool Bool (fun (b : Bool) => Bool.not b) (nat_eqb id id) Bool.true (nat_eqb_refl id)))
   (fresh_ctor_decls_head_family env id (CtorDecl.mk id ty) rest fresh))",
    ),
    (
        "fresh_ctor_decls_duplicate_refused",
        r"forall (env : KEnv) (family : Nat) (id : Nat) (ty : KExpr) (ty2 : KExpr) (rest : CtorDecls) (C : Prop),
FreshCtorDecls env family (CtorDecls.cons (CtorDecl.mk id ty) (CtorDecls.cons (CtorDecl.mk id ty2) rest)) -> C",
        r"fun (env : KEnv) (family : Nat) (id : Nat) (ty : KExpr) (ty2 : KExpr) (rest : CtorDecls) (C : Prop)
 (fresh : FreshCtorDecls env family (CtorDecls.cons (CtorDecl.mk id ty) (CtorDecls.cons (CtorDecl.mk id ty2) rest))) =>
bool_false_ne_true C
 (@Eq.trans Bool Bool.false (ctor_ids_fresh_b (CtorDecls.cons (CtorDecl.mk id ty2) rest) id) Bool.true
   (@Eq.symm Bool (ctor_ids_fresh_b (CtorDecls.cons (CtorDecl.mk id ty2) rest) id) Bool.false
     (ctor_ids_fresh_head_refused id ty2 rest))
   (fresh_ctor_decls_head_distinct env family (CtorDecl.mk id ty)
     (CtorDecls.cons (CtorDecl.mk id ty2) rest) fresh))",
    ),
    (
        "fresh_decl_occupied_refused",
        r"forall (env : KEnv) (id : Nat) (C : Prop),
@Eq Bool (kenv_fresh env id) Bool.false -> FreshDeclName env id -> C",
        r"fun (env : KEnv) (id : Nat) (C : Prop)
 (occupied : @Eq Bool (kenv_fresh env id) Bool.false) (fresh : FreshDeclName env id) =>
bool_false_ne_true C (@Eq.trans Bool Bool.false (kenv_fresh env id) Bool.true
 (@Eq.symm Bool (kenv_fresh env id) Bool.false occupied) fresh)",
    ),
    (
        "env_freshness_ctor_typed",
        r"forall (id : Nat),
CtorsWellTyped (Level.succ Level.zero) Nat.zero env_freshness_type (env_freshness_ctors id)",
        r"fun (id : Nat) =>
@CtorsWellTyped.cons (Level.succ Level.zero) Nat.zero env_freshness_type
 id (KExpr.bvar Nat.zero) (Level.succ Level.zero) CtorDecls.nil
 (CtxTyping.var (@ListType.cons KExpr env_freshness_type (@ListType.nil KExpr))
   Nat.zero env_freshness_type (CtxLookup.here env_freshness_type (@ListType.nil KExpr)))
 (@FieldsBounded.done_bvar (Level.succ Level.zero)
   (@ListType.cons KExpr env_freshness_type (@ListType.nil KExpr)) Nat.zero)
 (@CtorsWellTyped.nil (Level.succ Level.zero) Nat.zero env_freshness_type)",
    ),
    (
        "env_freshness_well_formed",
        r"forall (env : KEnv) (family : Nat) (id : Nat),
FreshCtorDecls env family (env_freshness_ctors id) ->
WellFormedCtorDecls env family Nat.zero env_freshness_type (env_freshness_ctors id)",
        r"fun (env : KEnv) (family : Nat) (id : Nat)
 (fresh : FreshCtorDecls env family (env_freshness_ctors id)) =>
@WellFormedCtorDecls.mk env family Nat.zero env_freshness_type (env_freshness_ctors id)
 (Level.succ Level.zero) fresh (@Eq.refl KExpr env_freshness_type)
 (@Eq.refl Bool Bool.true) (env_freshness_ctor_typed id)",
    ),
    (
        "env_freshness_extension",
        r"forall (env : KEnv) (family : Nat) (id : Nat),
FreshDeclName env family -> FreshCtorDecls env family (env_freshness_ctors id) ->
InductiveExtension env (KEnv.addInductive env family Nat.zero env_freshness_type (env_freshness_ctors id))",
        r"fun (env : KEnv) (family : Nat) (id : Nat) (hf : FreshDeclName env family)
 (hc : FreshCtorDecls env family (env_freshness_ctors id)) =>
@InductiveExtension.mk env family Nat.zero env_freshness_type (env_freshness_ctors id)
 (Level.succ (Level.succ Level.zero)) hf (Typing.sort (Level.succ Level.zero))
 (@Eq.refl Bool Bool.true) (env_freshness_well_formed env family id hc)",
    ),
    (
        "env_freshness_first_extension",
        r"InductiveExtension KEnv.empty env_freshness_first",
        r"env_freshness_extension KEnv.empty Nat.zero env_freshness_one
 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)",
    ),
    (
        "env_freshness_first_sound",
        r"EnvSound env_freshness_first",
        r"DefinitionalExtension.inductive_ KEnv.empty env_freshness_first env_freshness_first_extension",
    ),
    (
        "env_freshness_second_extension",
        r"InductiveExtension env_freshness_first env_freshness_second",
        r"env_freshness_extension env_freshness_first env_freshness_two env_freshness_three
 (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)",
    ),
    (
        "env_freshness_second_accepted",
        r"KernelAddDeclAccepts env_freshness_first env_freshness_second",
        r"@KernelAddDeclAccepts.inductive_case env_freshness_first env_freshness_second env_freshness_second_extension",
    ),
    (
        "env_freshness_acceptance_extends",
        r"DefinitionalExtension env_freshness_first env_freshness_second",
        r"kernel_add_decl_extends_env env_freshness_first env_freshness_second env_freshness_second_accepted",
    ),
    (
        "env_freshness_acceptance_preserves_sound",
        r"EnvSound env_freshness_second",
        r"KernelAddDeclPreservesEnvSound env_freshness_first env_freshness_second
 env_freshness_first_sound env_freshness_second_accepted",
    ),
    (
        "env_freshness_const_extension",
        r"ConstantExtension env_freshness_first env_freshness_const_result",
        r"@ConstantExtension.mk env_freshness_first ConstExtensionKind.reducible_ env_freshness_two
 env_freshness_type (KExpr.sort Level.zero) (Level.succ (Level.succ Level.zero))
 (@Eq.refl Bool Bool.true) (Typing.sort (Level.succ Level.zero)) (Typing.sort Level.zero)",
    ),
    (
        "env_freshness_const_accepted",
        r"KernelAddDeclAccepts env_freshness_first env_freshness_const_result",
        r"@KernelAddDeclAccepts.const_case env_freshness_first env_freshness_const_result env_freshness_const_extension",
    ),
    (
        "env_freshness_const_preserves_sound",
        r"EnvSound env_freshness_const_result",
        r"KernelAddDeclPreservesEnvSound env_freshness_first env_freshness_const_result
 env_freshness_first_sound env_freshness_const_accepted",
    ),
    (
        "env_freshness_stored_ctor_refused",
        r"@Eq Bool (kenv_fresh env_freshness_first env_freshness_one) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    (
        "env_freshness_existing_ctor_refused",
        r"@Eq Bool (ctor_decls_fresh_b env_freshness_first env_freshness_two (env_freshness_ctors env_freshness_one)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    (
        "env_freshness_existing_family_refused",
        r"@Eq Bool (ctor_decls_fresh_b env_freshness_first env_freshness_two (env_freshness_ctors Nat.zero)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    (
        "env_freshness_self_family_refused",
        r"@Eq Bool (ctor_decls_fresh_b KEnv.empty Nat.zero (env_freshness_ctors Nat.zero)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    (
        "env_freshness_intra_list_refused",
        r"@Eq Bool (ctor_decls_fresh_b KEnv.empty Nat.zero
 (CtorDecls.cons (CtorDecl.mk env_freshness_one (KExpr.bvar Nat.zero)) (env_freshness_ctors env_freshness_one))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    (
        "env_freshness_reducible_const_refused",
        r"@Eq Bool (ctor_decls_fresh_b
 (KEnv.addConst KEnv.empty ConstExtensionKind.reducible_ env_freshness_one env_freshness_type (KExpr.sort Level.zero))
 Nat.zero (env_freshness_ctors env_freshness_one)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    (
        "env_freshness_opaque_const_refused",
        r"@Eq Bool (ctor_decls_fresh_b
 (KEnv.addConst KEnv.empty ConstExtensionKind.opaque_ env_freshness_one env_freshness_type (KExpr.sort Level.zero))
 Nat.zero (env_freshness_ctors env_freshness_one)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    (
        "env_freshness_old_ctor_still_refused",
        r"@Eq Bool (kenv_fresh env_freshness_second env_freshness_one) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    (
        "env_freshness_nonadjacent_duplicate_refused",
        r"@Eq Bool (ctor_decls_fresh_b KEnv.empty Nat.zero
 (CtorDecls.cons (CtorDecl.mk env_freshness_one (KExpr.bvar Nat.zero))
   (CtorDecls.cons (CtorDecl.mk env_freshness_two (KExpr.bvar Nat.zero)) (env_freshness_ctors env_freshness_one)))) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
];

impl Specification {
    pub(super) fn add_env_freshness(&mut self) -> Result<(), SpecError> {
        for source in DATA {
            self.add_recursive_def(
                source,
                "Freshness control data: real model environments and constructor IDs.",
            )?;
        }
        for &(name, type_src, value_src) in PROOFS {
            super::acceptance_in::theorem(
                self, name, type_src, value_src,
                "Computed constructor freshness and distinctness, with actual new-declaration admission composition. No source-admission or idempotent-path claim.",
            )?;
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::{build_spec_with_stack, run_with_stack};
    use clean_kernel::{ConstantKind, ExprKind, Name};

    #[test]
    fn env_freshness_records_parse() {
        assert_eq!(DATA.len(), 8);
        assert_eq!(PROOFS.len(), 39);
        for source in DATA {
            clean_parser::parse_decl(source).expect("actual data declaration parses");
        }
        for &(name, ty, body) in PROOFS {
            clean_parser::parse_decl(&format!("def {name} : {ty} := {body}"))
                .expect("explicit checked proof record parses");
        }
    }

    #[test]
    fn env_freshness_actual_roots_recheck_without_axioms() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for &(name, ty, body) in PROOFS {
                let definition = spec.definitions().get(name).expect("registered proof");
                let kernel_name = Name::from_string(name);
                let constant = spec
                    .env()
                    .get_const(&kernel_name)
                    .expect("actual kernel root");
                let checked_type = definition.elaborated_type.as_ref().expect("checked type");
                let checked_value = definition.elaborated_value.as_ref().expect("checked value");
                assert!(!definition.is_axiom, "{name}");
                assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
                assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
                assert_eq!(
                    definition.proof_status,
                    ProofStatus::DerivedProved,
                    "{name}"
                );
                assert_eq!(definition.type_src, ty, "{name}");
                assert_eq!(definition.value_src.as_deref(), Some(body), "{name}");
                assert_eq!(&constant.type_, checked_type, "{name}");
                assert_eq!(constant.value.as_ref(), Some(checked_value), "{name}");
                assert!(
                    !matches!(checked_value.kind(), ExprKind::Const(n, _) if n == &kernel_name),
                    "{name}"
                );
                spec.verify_definition(name)
                    .expect("actual theorem rechecks");
                assert!(
                    spec.env()
                        .axiom_deps(&kernel_name)
                        .expect("domain closure")
                        .is_empty(),
                    "{name}"
                );
                assert!(
                    spec.env()
                        .foundational_axiom_deps(&kernel_name)
                        .expect("foundation closure")
                        .is_empty(),
                    "{name}"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
            // The pre-existing nonvacuity witness was repaired, not deleted.
            let witness = "well_formed_ctor_decls_nonvacuity_witness";
            let definition = spec.definitions().get(witness).expect("original witness");
            assert!(definition
                .type_src
                .contains("CtorDecl.mk (Nat.succ Nat.zero)"));
            assert!(definition.type_src.contains("KEnv.empty Nat.zero Nat.zero"));
            spec.verify_definition(witness)
                .expect("fresh family0/ctor1 witness rechecks");
            assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, witness).is_empty());
        });
    }

    #[test]
    fn env_freshness_refuses_collision_guards_and_admissions() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                r"def env_freshness_forged_existing_ctor : FreshCtorDecls env_freshness_first env_freshness_two (env_freshness_ctors env_freshness_one) := @Eq.refl Bool Bool.true",
                r"def env_freshness_forged_self_family : FreshCtorDecls KEnv.empty Nat.zero (env_freshness_ctors Nat.zero) := @Eq.refl Bool Bool.true",
                r"def env_freshness_forged_duplicate : FreshCtorDecls KEnv.empty Nat.zero (CtorDecls.cons (CtorDecl.mk env_freshness_one (KExpr.bvar Nat.zero)) (env_freshness_ctors env_freshness_one)) := @Eq.refl Bool Bool.true",
                r"def env_freshness_forged_family : FreshDeclName env_freshness_first env_freshness_one := @Eq.refl Bool Bool.true",
                r"def env_freshness_forged_inductive : InductiveExtension env_freshness_first (KEnv.addInductive env_freshness_first env_freshness_two Nat.zero env_freshness_type (env_freshness_ctors env_freshness_one)) := env_freshness_extension env_freshness_first env_freshness_two env_freshness_one (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)",
                r"def env_freshness_forged_reducible : ConstantExtension env_freshness_first (KEnv.addConst env_freshness_first ConstExtensionKind.reducible_ env_freshness_one env_freshness_type (KExpr.sort Level.zero)) := ConstantExtension.mk env_freshness_first ConstExtensionKind.reducible_ env_freshness_one env_freshness_type (KExpr.sort Level.zero) (Level.succ (Level.succ Level.zero)) (@Eq.refl Bool Bool.true) (Typing.sort (Level.succ Level.zero)) (Typing.sort Level.zero)",
                r"def env_freshness_forged_opaque : ConstantExtension env_freshness_first (KEnv.addConst env_freshness_first ConstExtensionKind.opaque_ env_freshness_one env_freshness_type (KExpr.sort Level.zero)) := ConstantExtension.mk env_freshness_first ConstExtensionKind.opaque_ env_freshness_one env_freshness_type (KExpr.sort Level.zero) (Level.succ (Level.succ Level.zero)) (@Eq.refl Bool Bool.true) (Typing.sort (Level.succ Level.zero)) (Typing.sort Level.zero)",
            ] {
                let clean_parser::SurfaceDecl::Def { name, .. } =
                    clean_parser::parse_decl(source).expect("negative control must parse")
                else {
                    panic!("expected a definition");
                };
                let error = spec
                    .add_recursive_def(source, "Well-parsed collision control.")
                    .expect_err("occupied, self-family or duplicate identifier must be refused");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
                // Legacy record-key projection only; exact kernel identity is checked separately.
                assert!(
                    !spec.definitions().contains_key(
                        &name
                            .qualify_under(&Default::default())
                            .into_name()
                            .to_string()
                    ),
                    "{name}"
                );
                assert!(
                    spec.env()
                        .get_const(&name.qualify_under(&Default::default()).into_name())
                        .is_none(),
                    "{name}"
                );
            }
        });
    }
}

#[cfg(test)]
#[path = "env_freshness_strict_tests.rs"]
mod strict_tests;

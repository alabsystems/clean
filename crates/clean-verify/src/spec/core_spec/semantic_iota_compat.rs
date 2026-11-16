// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic replacement for the actual guarded iota_reduct model.
//!
//! The same five lookup keys and list shape preserve metadata, rule and major.
//! Both actual guards are transported, and existing semantic substitution proves
//! related once-instantiated RHS values. No support, output-step or typing
//! premise is added to the generic simulation theorem.
//!
//! This remains a bounded model result: constructor universes and production
//! modes/prepasses are not implemented by this operator. It is not admission,
//! semantic confluence, or Trust/Rust refinement. Registered construction and
//! complete independent replay remain separate integration gates.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Requires semantic_spine_compat, pure semantic_head_discriminators, the
    /// actual iota_reduct_full_inv_type and iota_reduct_full_recon, plus
    /// option injectivity/empty discrimination. No operational delta theorem.
    pub(super) fn add_semantic_iota_compat(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def kexprUniverseEq_head_name (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (kexpr_const_name (kapp_fn e2)) :=
 kexprUniverseEq_const_name (kapp_fn e) (kapp_fn e2) (kexprUniverseEq_kapp_fn e e2 h)",
            "The actual recursor/constructor head-name lookup keys are exactly preserved.",
        )?;

        self.add_recursive_def(
            r"def kexprListUniverseEq_head_some (xs : ListType KExpr) (xs2 : ListType KExpr)
 (a : KExpr) (C : Type) (h : KExprListUniverseEq xs xs2)
 (get : @Eq (OptionType KExpr) (list_head xs) (@OptionType.some KExpr a))
 (consume : forall (a2 : KExpr), @Eq (OptionType KExpr) (list_head xs2) (@OptionType.some KExpr a2) ->
   KExprUniverseEq a a2 -> C) : C :=
 @KExprListUniverseEq.rec
 (fun (ys : ListType KExpr) (ys2 : ListType KExpr) (_ : KExprListUniverseEq ys ys2) =>
   forall (x : KExpr), @Eq (OptionType KExpr) (list_head ys) (@OptionType.some KExpr x) ->
   (forall (x2 : KExpr), @Eq (OptionType KExpr) (list_head ys2) (@OptionType.some KExpr x2) ->
      KExprUniverseEq x x2 -> C) -> C)
 (fun (x : KExpr) (empty : @Eq (OptionType KExpr) (list_head (@ListType.nil KExpr)) (@OptionType.some KExpr x))
   (_consume : forall (x2 : KExpr), @Eq (OptionType KExpr) (list_head (@ListType.nil KExpr)) (@OptionType.some KExpr x2) ->
     KExprUniverseEq x x2 -> C) => option_none_ne_some_type KExpr x C empty)
 (fun (x : KExpr) (x2 : KExpr) (ys : ListType KExpr) (ys2 : ListType KExpr)
   (hx : KExprUniverseEq x x2) (_hy : KExprListUniverseEq ys ys2)
   (_ih : forall (z : KExpr), @Eq (OptionType KExpr) (list_head ys) (@OptionType.some KExpr z) ->
     (forall (z2 : KExpr), @Eq (OptionType KExpr) (list_head ys2) (@OptionType.some KExpr z2) ->
       KExprUniverseEq z z2 -> C) -> C)
   (z : KExpr) (first : @Eq (OptionType KExpr) (list_head (@ListType.cons KExpr x ys)) (@OptionType.some KExpr z))
   (next : forall (z2 : KExpr), @Eq (OptionType KExpr) (list_head (@ListType.cons KExpr x2 ys2)) (@OptionType.some KExpr z2) ->
     KExprUniverseEq z z2 -> C) =>
   next x2 (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr x2))
     (Eq.substType KExpr (fun (z0 : KExpr) => KExprUniverseEq z0 x2) x z
       (option_some_inj KExpr x z first) hx)) xs xs2 h a get consume",
            "A successful actual list_head lookup transfers to a related witness on the other list, by relation inversion and option injectivity.",
        )?;

        self.add_recursive_def(
            r"def kexprListUniverseEq_drop_equal_counts (n : Nat) (m : Nat)
 (counts : @Eq Nat n m) (xs : ListType KExpr) (xs2 : ListType KExpr)
 (h : KExprListUniverseEq xs xs2) :
 KExprListUniverseEq (list_drop n xs) (list_drop m xs2) :=
 Eq.substType Nat
   (fun (j : Nat) => KExprListUniverseEq (list_drop n xs) (list_drop j xs2))
   n m counts (kexprListUniverseEq_drop n xs xs2 h)",
            "Dropping provably equal computed counts preserves the list relation; used for length-minus-field-count selection.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_head_levels (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 LevelListEqSem (kexpr_const_levels (kapp_fn e)) (kexpr_const_levels (kapp_fn e2)) :=
 kexprUniverseEq_const_levels (kapp_fn e) (kapp_fn e2) (kexprUniverseEq_kapp_fn e e2 h)",
            "Actual recursor head universe lists are related; their exact shape supplies guard preservation.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fields_guard (rule : RecRule) (major : KExpr) (major2 : KExpr)
 (hmajor : KExprUniverseEq major major2)
 (accepted : @Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true) :
 @Eq Bool (iota_fields_ok rule (kapp_args major2)) Bool.true :=
 Eq.trans Bool (iota_fields_ok rule (kapp_args major2)) (iota_fields_ok rule (kapp_args major)) Bool.true
  (Eq.symm Bool (iota_fields_ok rule (kapp_args major)) (iota_fields_ok rule (kapp_args major2))
   (Eq.cong Nat Bool (fun (len : Nat) => nat_eqb (Nat.sub (recrule_num_fields rule) len) Nat.zero)
    (list_length (kapp_args major)) (list_length (kapp_args major2)) (kexprListUniverseEq_length (kapp_args major) (kapp_args major2) (kexprUniverseEq_kapp_args major major2 hmajor)))) accepted",
            "Field availability survives semantic replacement because the actual constructor spine has the same length.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_arity_guard (md : RecMeta) (e : KExpr) (e2 : KExpr)
 (he : KExprUniverseEq e e2)
 (accepted : @Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true) :
 @Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn e2)))) Bool.true :=
 Eq.trans Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn e2))))
  (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true
  (Eq.cong Nat Bool (fun (len : Nat) => nat_eqb (name_list_len (kconst_params (recmeta_signature md))) len)
   (level_list_len (kexpr_const_levels (kapp_fn e2))) (level_list_len (kexpr_const_levels (kapp_fn e)))
   (Eq.symm Nat (level_list_len (kexpr_const_levels (kapp_fn e))) (level_list_len (kexpr_const_levels (kapp_fn e2)))
    (levelListEqSem_length (kexpr_const_levels (kapp_fn e)) (kexpr_const_levels (kapp_fn e2)) (semantic_iota_head_levels e e2 he)))) accepted",
            "Actual stored-signature/head-argument arity remains successful under equal-shape semantic level lists.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_contractum_compat (e : KExpr) (e2 : KExpr) (he : KExprUniverseEq e e2)
 (major : KExpr) (major2 : KExpr) (hmajor : KExprUniverseEq major major2)
 (md : RecMeta) (rule : RecRule) (body : KExpr) (body2 : KExpr)
 (hbody : KExprUniverseEq body body2) :
 KExprUniverseEq (iota_contractum md rule (kapp_args e) (kapp_args major) (body)) (iota_contractum md rule (kapp_args e2) (kapp_args major2) (body2)) :=
 kexprUniverseEq_apply_spine (list_drop (Nat.succ (iota_major_index md)) (kapp_args e)) (list_drop (Nat.succ (iota_major_index md)) (kapp_args e2)) (kexprListUniverseEq_drop (Nat.succ (iota_major_index md)) (kapp_args e) (kapp_args e2) (kexprUniverseEq_kapp_args e e2 he)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (apply_spine (list_take (iota_prefix_count md) (kapp_args e)) body)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (apply_spine (list_take (iota_prefix_count md) (kapp_args e2)) body2)) (kexprUniverseEq_apply_spine (list_drop (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule)) (kapp_args major)) (list_drop (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule)) (kapp_args major2)) (kexprListUniverseEq_drop_equal_counts
 (Nat.sub (list_length (kapp_args major)) (recrule_num_fields rule))
 (Nat.sub (list_length (kapp_args major2)) (recrule_num_fields rule))
 (Eq.cong Nat Nat (fun (len : Nat) => Nat.sub len (recrule_num_fields rule))
  (list_length (kapp_args major)) (list_length (kapp_args major2)) (kexprListUniverseEq_length (kapp_args major) (kapp_args major2) (kexprUniverseEq_kapp_args major major2 hmajor)))
 (kapp_args major) (kapp_args major2) (kexprUniverseEq_kapp_args major major2 hmajor)) (apply_spine (list_take (iota_prefix_count md) (kapp_args e)) body) (apply_spine (list_take (iota_prefix_count md) (kapp_args e2)) body2) (kexprUniverseEq_apply_spine (list_take (iota_prefix_count md) (kapp_args e)) (list_take (iota_prefix_count md) (kapp_args e2)) (kexprListUniverseEq_take (iota_prefix_count md) (kapp_args e) (kapp_args e2) (kexprUniverseEq_kapp_args e e2 he)) (body) (body2) (hbody)))",
            "The actual contractum preserves related supplied RHS instances and related prefix, field and extra spines; no raw-template reflexivity or step premise is assumed.",
        )?;

        self.add_recursive_def(
            r"def iota_reduct_universe_compat (env : RecEnv) (e : KExpr) (e2 : KExpr) (r : KExpr)
 (he : KExprUniverseEq e e2)
 (hstep : @Eq (OptionType KExpr) (iota_reduct env e) (@OptionType.some KExpr r))
 (C : Type) (consume : forall (r2 : KExpr),
   @Eq (OptionType KExpr) (iota_reduct env e2) (@OptionType.some KExpr r2) ->
   KExprUniverseEq r r2 -> C) : C :=
 iota_reduct_full_inv_type env e r C hstep
 (fun (recname : Name) (md : RecMeta) (major : KExpr) (cname : Name) (rule : RecRule)
  (h1 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname))
  (h2 : @Eq (OptionType RecMeta) (recmeta_for env recname) (@OptionType.some RecMeta md))
  (h3 : @Eq (OptionType KExpr) (list_head (list_drop (iota_major_index md) (kapp_args e))) (@OptionType.some KExpr major))
  (h4 : @Eq (OptionType Name) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname))
  (h5 : @Eq (OptionType RecRule) (recrule_for env recname cname) (@OptionType.some RecRule rule))
  (hfields : @Eq Bool (iota_fields_ok rule (kapp_args major)) Bool.true)
  (harity : @Eq Bool (nat_eqb (name_list_len (kconst_params (recmeta_signature md))) (level_list_len (kexpr_const_levels (kapp_fn e)))) Bool.true)
  (returned : @Eq KExpr r (iota_contractum md rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))))) =>
  kexprListUniverseEq_head_some (list_drop (iota_major_index md) (kapp_args e))
   (list_drop (iota_major_index md) (kapp_args e2)) major C
   (kexprListUniverseEq_drop (iota_major_index md) (kapp_args e) (kapp_args e2) (kexprUniverseEq_kapp_args e e2 he)) h3
   (fun (major2 : KExpr)
    (h3new : @Eq (OptionType KExpr) (list_head (list_drop (iota_major_index md) (kapp_args e2))) (@OptionType.some KExpr major2))
    (hmajor : KExprUniverseEq major major2) =>
    consume (iota_contractum md rule (kapp_args e2) (kapp_args major2) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e2))))
     (iota_reduct_full_recon env e2 (iota_contractum md rule (kapp_args e2) (kapp_args major2) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e2)))) recname md major2 cname rule
      (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn e2)) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name recname)
       (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (kexpr_const_name (kapp_fn e2)) (kexprUniverseEq_head_name e e2 he)) h1)
      h2 h3new
      (Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn major2)) (kexpr_const_name (kapp_fn major)) (@OptionType.some Name cname)
       (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn major)) (kexpr_const_name (kapp_fn major2)) (kexprUniverseEq_head_name major major2 hmajor)) h4)
      h5 (semantic_iota_fields_guard rule major major2 hmajor hfields)
      (semantic_iota_arity_guard md e e2 he harity) (@Eq.refl KExpr (iota_contractum md rule (kapp_args e2) (kapp_args major2) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e2))))))
     (Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq out (iota_contractum md rule (kapp_args e2) (kapp_args major2) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e2))))) (iota_contractum md rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) r
      (Eq.symm KExpr r (iota_contractum md rule (kapp_args e) (kapp_args major) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)))) returned)
      (semantic_iota_contractum_compat e e2 he major major2 hmajor md rule (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e))) (recursor_rhs_instance (recmeta_signature md) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e2)))
       (instLevels_semantic_values (kconst_params (recmeta_signature md)) (recrule_rhs rule) (kexpr_const_levels (kapp_fn e)) (kexpr_const_levels (kapp_fn e2))
        (semantic_iota_head_levels e e2 he))))))",
            "Successful actual guarded iota transfers under semantic replacement without any environment-support premise: exact names preserve lookups, actual lengths preserve both guards, and semantic substitution relates the once-instantiated RHS values.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_rec : Name := Name.anonymous",
            "Model-only fixture recursor lookup key.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_ctor : Name := Name.str Name.anonymous Nat.zero",
            "Distinct model-only constructor lookup key.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_meta : RecMeta := RecMeta.mk (Nat.succ Nat.zero) Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Bool.true (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous))) Nat.zero",
            "Reduction-only fixture metadata: one parameter, zero motives, one minor, one index, then major and extras. The stored singleton-parameter signature is synthetic data, not an admitted recursor type; active iota uses its ordered parameters and arity; no type-validity claim follows.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_rhs : KExpr := KExpr.sort (Level.param Name.anonymous)",
            "A stored schematic RHS whose parameter is instantiated once at the actual recursor head level.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_rule : RecRule := RecRule.mk semantic_iota_fixture_ctor (Nat.succ Nat.zero) semantic_iota_fixture_rhs",
            "A single-field rule; the constructor also receives a separate parameter that the actual field selection must drop.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_env : RecEnv := RecEnv.addRec RecEnv.empty semantic_iota_fixture_rec semantic_iota_fixture_meta (RecRules.cons semantic_iota_fixture_rule RecRules.nil)",
            "Concrete supplied recursor environment with distinct recursor/constructor keys and one actual rule.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_term (us : ListType Level) (vs : ListType Level) (u : Level) : KExpr := (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_rec us) (KExpr.sort u)) (KExpr.lit Nat.zero)) (KExpr.lit (Nat.succ Nat.zero))) (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_ctor vs) (KExpr.lit (Nat.succ (Nat.succ Nat.zero)))) (KExpr.sort u))) (KExpr.lit (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
            "The actual spine has parameter, minor, index, a constructor with parameter/field, then extra; raw universe lists remain separately observable syntax.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_result (u : Level) : KExpr := (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.sort u) (KExpr.sort u)) (KExpr.lit Nat.zero)) (KExpr.sort u)) (KExpr.lit (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
            "Expected guarded contractum: the instantiated RHS sort receives parameter, minor, field and extra in order; index and constructor parameter are excluded.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_success (vs : ListType Level) (u : Level) :
 @Eq (OptionType KExpr) (iota_reduct semantic_iota_fixture_env
   (semantic_iota_fixture_term (@ListType.cons Level u (@ListType.nil Level)) vs u))
   (@OptionType.some KExpr (semantic_iota_fixture_result u)) :=
 @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (semantic_iota_fixture_result u))",
            "Actual singleton head arity succeeds and instantiates the stored parameter once; constructor universe lists remain uninspected by this bounded operator.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_related (us : ListType Level) (us2 : ListType Level) (hus : LevelListEqSem us us2)
 (vs : ListType Level) (vs2 : ListType Level) (hvs : LevelListEqSem vs vs2)
 (u : Level) (u2 : Level) (hu : levelEqSem u u2) :
 KExprUniverseEq (semantic_iota_fixture_term us vs u) (semantic_iota_fixture_term us2 vs2 u2) :=
 (KExprUniverseEq.app (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_rec us) (KExpr.sort u)) (KExpr.lit Nat.zero)) (KExpr.lit (Nat.succ Nat.zero))) (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_ctor vs) (KExpr.lit (Nat.succ (Nat.succ Nat.zero)))) (KExpr.sort u))) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_rec us2) (KExpr.sort u2)) (KExpr.lit Nat.zero)) (KExpr.lit (Nat.succ Nat.zero))) (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_ctor vs2) (KExpr.lit (Nat.succ (Nat.succ Nat.zero)))) (KExpr.sort u2))) (KExpr.lit (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.lit (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExprUniverseEq.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_rec us) (KExpr.sort u)) (KExpr.lit Nat.zero)) (KExpr.lit (Nat.succ Nat.zero))) (KExpr.app (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_rec us2) (KExpr.sort u2)) (KExpr.lit Nat.zero)) (KExpr.lit (Nat.succ Nat.zero))) (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_ctor vs) (KExpr.lit (Nat.succ (Nat.succ Nat.zero)))) (KExpr.sort u)) (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_ctor vs2) (KExpr.lit (Nat.succ (Nat.succ Nat.zero)))) (KExpr.sort u2)) (KExprUniverseEq.app (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_rec us) (KExpr.sort u)) (KExpr.lit Nat.zero)) (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_rec us2) (KExpr.sort u2)) (KExpr.lit Nat.zero)) (KExpr.lit (Nat.succ Nat.zero)) (KExpr.lit (Nat.succ Nat.zero)) (KExprUniverseEq.app (KExpr.app (KExpr.const semantic_iota_fixture_rec us) (KExpr.sort u)) (KExpr.app (KExpr.const semantic_iota_fixture_rec us2) (KExpr.sort u2)) (KExpr.lit Nat.zero) (KExpr.lit Nat.zero) (KExprUniverseEq.app (KExpr.const semantic_iota_fixture_rec us) (KExpr.const semantic_iota_fixture_rec us2) (KExpr.sort u) (KExpr.sort u2) (KExprUniverseEq.const semantic_iota_fixture_rec us us2 hus) (KExprUniverseEq.sort u u2 hu)) (KExprUniverseEq.lit Nat.zero)) (KExprUniverseEq.lit (Nat.succ Nat.zero))) (KExprUniverseEq.app (KExpr.app (KExpr.const semantic_iota_fixture_ctor vs) (KExpr.lit (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const semantic_iota_fixture_ctor vs2) (KExpr.lit (Nat.succ (Nat.succ Nat.zero)))) (KExpr.sort u) (KExpr.sort u2) (KExprUniverseEq.app (KExpr.const semantic_iota_fixture_ctor vs) (KExpr.const semantic_iota_fixture_ctor vs2) (KExpr.lit (Nat.succ (Nat.succ Nat.zero))) (KExpr.lit (Nat.succ (Nat.succ Nat.zero))) (KExprUniverseEq.const semantic_iota_fixture_ctor vs vs2 hvs) (KExprUniverseEq.lit (Nat.succ (Nat.succ Nat.zero)))) (KExprUniverseEq.sort u u2 hu))) (KExprUniverseEq.lit (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
            "Constructed semantic relation for the actual nested fixture, preserving every name, literal payload, field position and universe-list shape.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_output_relation (u : Level) (u2 : Level) (hu : levelEqSem u u2) :
 KExprUniverseEq (semantic_iota_fixture_result u) (semantic_iota_fixture_result u2) :=
 iota_reduct_universe_compat semantic_iota_fixture_env (semantic_iota_fixture_term (@ListType.cons Level u (@ListType.nil Level)) (@ListType.cons Level u (@ListType.nil Level)) u) (semantic_iota_fixture_term (@ListType.cons Level u2 (@ListType.nil Level)) (@ListType.cons Level u2 (@ListType.nil Level)) u2)
   (semantic_iota_fixture_result u)
   (semantic_iota_fixture_related (@ListType.cons Level u (@ListType.nil Level)) (@ListType.cons Level u2 (@ListType.nil Level)) (LevelListEqSem.cons u u2 (@ListType.nil Level) (@ListType.nil Level) hu LevelListEqSem.nil)
     (@ListType.cons Level u (@ListType.nil Level)) (@ListType.cons Level u2 (@ListType.nil Level)) (LevelListEqSem.cons u u2 (@ListType.nil Level) (@ListType.nil Level) hu LevelListEqSem.nil) u u2 hu)
   (semantic_iota_fixture_success (@ListType.cons Level u (@ListType.nil Level)) u)
   (KExprUniverseEq (semantic_iota_fixture_result u) (semantic_iota_fixture_result u2))
   (fun (out : KExpr)
     (hout : @Eq (OptionType KExpr) (iota_reduct semantic_iota_fixture_env (semantic_iota_fixture_term (@ListType.cons Level u2 (@ListType.nil Level)) (@ListType.cons Level u2 (@ListType.nil Level)) u2)) (@OptionType.some KExpr out))
     (hrel : KExprUniverseEq (semantic_iota_fixture_result u) out) =>
     Eq.substType KExpr (fun (out2 : KExpr) => KExprUniverseEq (semantic_iota_fixture_result u) out2)
       out (semantic_iota_fixture_result u2)
       (option_some_inj KExpr out (semantic_iota_fixture_result u2)
         (Eq.trans (OptionType KExpr) (@OptionType.some KExpr out)
           (iota_reduct semantic_iota_fixture_env (semantic_iota_fixture_term (@ListType.cons Level u2 (@ListType.nil Level)) (@ListType.cons Level u2 (@ListType.nil Level)) u2))
           (@OptionType.some KExpr (semantic_iota_fixture_result u2))
           (Eq.symm (OptionType KExpr) (iota_reduct semantic_iota_fixture_env (semantic_iota_fixture_term (@ListType.cons Level u2 (@ListType.nil Level)) (@ListType.cons Level u2 (@ListType.nil Level)) u2))
             (@OptionType.some KExpr out) hout)
           (semantic_iota_fixture_success (@ListType.cons Level u2 (@ListType.nil Level)) u2))) hrel)",
            "The actual generic simulation theorem is consumed by a fully constructed guarded fixture and identifies its output through deterministic computed lookup.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_imax_zero (u : Level) :
 KExprUniverseEq (semantic_iota_fixture_result (Level.imax u Level.zero))
   (semantic_iota_fixture_result Level.zero) :=
 semantic_iota_fixture_output_relation (Level.imax u Level.zero) Level.zero
   (fun (v : Name -> Nat) => @Eq.refl Nat Nat.zero)",
            "Nontrivial semantic replacement of recursor levels, constructor levels, prefix and field sorts, through the actual successful iota simulation caller.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_missing_major :
 @Eq (OptionType KExpr) (iota_reduct semantic_iota_fixture_env (KExpr.app (KExpr.app (KExpr.app (KExpr.const semantic_iota_fixture_rec (@ListType.nil Level)) (KExpr.sort Level.zero)) (KExpr.lit Nat.zero)) (KExpr.lit (Nat.succ Nat.zero)))) (@OptionType.none KExpr) :=
 @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "The actual major-position lookup refuses the truncated prefix/minor/index spine; no dummy major is inserted.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_missing_rule (u : Level) :
 @Eq (OptionType KExpr)
   (iota_reduct (RecEnv.addRec RecEnv.empty semantic_iota_fixture_rec semantic_iota_fixture_meta RecRules.nil)
     (semantic_iota_fixture_term (@ListType.cons Level u (@ListType.nil Level)) (@ListType.cons Level u (@ListType.nil Level)) u)) (@OptionType.none KExpr) :=
 @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "Metadata success does not manufacture a constructor rule: the actual empty rule table returns none.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_missing_rec (u : Level) :
 @Eq (OptionType KExpr) (iota_reduct RecEnv.empty (semantic_iota_fixture_term (@ListType.cons Level u (@ListType.nil Level)) (@ListType.cons Level u (@ListType.nil Level)) u)) (@OptionType.none KExpr) :=
 @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "A missing recursor metadata entry is an actual refusal in the same fixture.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_constructor_universe_erasure (vs : ListType Level) (u : Level) :
 @Eq (OptionType KExpr)
  (iota_reduct semantic_iota_fixture_env (semantic_iota_fixture_term (@ListType.cons Level u (@ListType.nil Level)) vs u))
  (iota_reduct semantic_iota_fixture_env (semantic_iota_fixture_term (@ListType.cons Level u (@ListType.nil Level)) (@ListType.nil Level) u)) :=
 @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (semantic_iota_fixture_result u))",
            "The bounded operator still ignores constructor head universe lists, but NOT recursor arity or RHS instantiation. This remaining source-fidelity boundary is explicit.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_missing_universe (vs : ListType Level) (u : Level) :
 @Eq (OptionType KExpr) (iota_reduct semantic_iota_fixture_env
  (semantic_iota_fixture_term (@ListType.nil Level) vs u)) (@OptionType.none KExpr) :=
 @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "Actual recursor arity guard refuses a missing head universe after all five lookups succeed.",
        )?;

        self.add_recursive_def(
            r"def semantic_iota_fixture_extra_universe (vs : ListType Level) (u : Level) :
 @Eq (OptionType KExpr) (iota_reduct semantic_iota_fixture_env
  (semantic_iota_fixture_term (@ListType.cons Level u (@ListType.cons Level u (@ListType.nil Level))) vs u)) (@OptionType.none KExpr) :=
 @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "Actual recursor arity guard refuses an extra head universe rather than silently erasing it.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn semantic_iota_simulation_and_actual_model_controls_are_checked() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for name in [
                "kexprUniverseEq_head_name",
                "kexprListUniverseEq_head_some",
                "kexprListUniverseEq_drop_equal_counts",
                "semantic_iota_head_levels",
                "semantic_iota_fields_guard",
                "semantic_iota_arity_guard",
                "semantic_iota_contractum_compat",
                "iota_reduct_universe_compat",
                "semantic_iota_fixture_success",
                "semantic_iota_fixture_related",
                "semantic_iota_fixture_output_relation",
                "semantic_iota_fixture_imax_zero",
                "semantic_iota_fixture_missing_major",
                "semantic_iota_fixture_missing_rule",
                "semantic_iota_fixture_missing_rec",
                "semantic_iota_fixture_constructor_universe_erasure",
                "semantic_iota_fixture_missing_universe",
                "semantic_iota_fixture_extra_universe",
            ] {
                let declaration = spec
                    .definitions()
                    .get(name)
                    .expect("registered semantic iota proof");
                assert!(!declaration.is_axiom, "{name}");
                assert!(declaration.elaborated_value.is_some(), "{name}");
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
        });
    }

    #[test]
    fn semantic_iota_cannot_forge_missing_guards_or_drop_all_output_arguments() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                "def semantic_iota_forged_missing_rec : @Eq (OptionType KExpr) (iota_reduct RecEnv.empty (semantic_iota_fixture_term (@ListType.cons Level Level.zero (@ListType.nil Level)) (@ListType.nil Level) Level.zero)) (@OptionType.some KExpr (semantic_iota_fixture_result Level.zero)) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (semantic_iota_fixture_result Level.zero))",
                "def semantic_iota_forged_missing_rule : @Eq (OptionType KExpr) (iota_reduct (RecEnv.addRec RecEnv.empty semantic_iota_fixture_rec semantic_iota_fixture_meta RecRules.nil) (semantic_iota_fixture_term (@ListType.cons Level Level.zero (@ListType.nil Level)) (@ListType.nil Level) Level.zero)) (@OptionType.some KExpr (semantic_iota_fixture_result Level.zero)) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (semantic_iota_fixture_result Level.zero))",
                "def semantic_iota_forged_output : @Eq (OptionType KExpr) (iota_reduct semantic_iota_fixture_env (semantic_iota_fixture_term (@ListType.cons Level Level.zero (@ListType.nil Level)) (@ListType.nil Level) Level.zero)) (@OptionType.some KExpr semantic_iota_fixture_rhs) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr semantic_iota_fixture_rhs)",
            ] {
                assert!(spec.add_recursive_def(source, "Negative current-model iota control.").is_err(),
                    "actual iota guard and exact reassembly must remain enforced");
            }
        });
    }
}

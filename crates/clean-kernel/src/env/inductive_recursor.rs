// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursor generation for inductive types.
//!
//! Builds `.rec`, `.casesOn`, and `.recOn` for each inductive type.
//! Extracted from `inductive_builder.rs` for maintainability.
//!
//! Type construction is in `inductive_recursor_types.rs`.
//! Rule RHS construction and BVar remapping is in `inductive_recursor_rules.rs`.

use crate::expr::{BinderData, BinderInfo, Expr, ExprKind};
use crate::inductive::{
    consume_type_annotations, count_pi_args, get_return_type, InductiveDecl, InductiveError,
    InductiveType, RecursorArgOrder, RecursorRule, RecursorVal,
};
use crate::level::Level;
use crate::name::Name;
use crate::tc::is_prop_type;
use std::sync::Arc;

use super::elim_analysis::elim_only_at_universe_zero;
use super::inductive_fixed_indices::{fresh_univ_name, CtorInfo};
use super::types::EnvError;
use super::Environment;

impl Environment {
    /// Compute constructor field information shared by all builders (rec, casesOn, recOn).
    ///
    /// Returns (name, num_fields, recursive_flags, field_types, return_indices) for each
    /// constructor. Called once per inductive type in `add_inductive`, avoiding redundant
    /// traversals of constructor types across the three builder methods.
    pub(crate) fn compute_ctor_infos(
        &self,
        ind_type: &InductiveType,
        decl: &InductiveDecl,
    ) -> Vec<CtorInfo> {
        use std::collections::HashSet;
        let ind_name_set: HashSet<&Name> = decl.types.iter().map(|t| &t.name).collect();
        let mut ctor_infos = Vec::with_capacity(ind_type.constructors.len());
        for ctor in &ind_type.constructors {
            let ctor_arity = count_pi_args(&ctor.type_);
            let num_fields = ctor_arity.saturating_sub(decl.num_params);
            let recursive_flags =
                self.get_recursive_field_flags(&ctor.type_, &ind_name_set, decl.num_params);
            let field_types = self.get_constructor_field_types(&ctor.type_, decl.num_params);
            let return_indices = self.get_constructor_return_indices(&ctor.type_, decl.num_params);
            ctor_infos.push((
                ctor.name.clone(),
                num_fields,
                recursive_flags,
                field_types,
                return_indices,
            ));
        }
        ctor_infos
    }

    /// Build a recursor for an inductive type.
    ///
    /// For mutual inductives (Lean 4 inductive.cpp:752-776), the recursor includes:
    /// - One motive per type in the mutual block (`num_motives = decl.types.len()`)
    /// - Minor premises for ALL constructors across ALL types
    /// - Rules only for this type's constructors (indexed globally via `minor_idx_offset`)
    pub(crate) fn build_recursor(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        ctor_infos: &[CtorInfo],
        all_ctor_infos: &[CtorInfo],
        minor_idx_offset: usize,
    ) -> Result<RecursorVal, EnvError> {
        let ind_type = decl
            .types
            .iter()
            .find(|t| &t.name == ind_name)
            .ok_or_else(|| EnvError::UnknownInductive(ind_name.clone()))?;

        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

        // Lean 4: for Prop-valued inductives that can only eliminate into Prop,
        // the recursor does NOT get an extra motive universe parameter.
        let prop_only = elim_only_at_universe_zero(
            self,
            &ind_type.type_,
            &ind_type.constructors,
            decl.num_params,
            decl.types.len(),
        );

        let (motive_univ_name_opt, rec_level_params) = if prop_only {
            (None, decl.level_params.clone())
        } else {
            let motive_univ_name = fresh_univ_name(&decl.level_params);
            let mut params = vec![motive_univ_name.clone()];
            params.extend(decl.level_params.clone());
            (Some(motive_univ_name), params)
        };

        let type_arity = count_pi_args(&ind_type.type_);
        let num_indices = type_arity.saturating_sub(decl.num_params);

        // For mutual inductives, motives cover ALL types, minors cover ALL constructors.
        // Reference: Lean 4 declare_recursors() uses collect_Cs (all motives) and
        // collect_minor_premises (all minors from all types).
        let num_motives = decl.types.len() as u32;
        let total_minors = all_ctor_infos.len();

        // Build recursor type with all motives and all minors
        let rec_ty = self.build_recursor_type(
            ind_name,
            &ind_type.type_,
            decl.num_params,
            num_indices,
            motive_univ_name_opt.as_ref(),
            &decl.level_params,
            all_ctor_infos,
            &decl.types,
        );

        // Build recursor rules.
        // Each recursor has rules for THIS type's constructors only.
        // The minor index is offset by minor_idx_offset to account for
        // constructors of other types in the mutual block.
        let rules: Vec<RecursorRule> = ctor_infos
            .iter()
            .enumerate()
            .map(
                |(idx, (ctor_name, num_fields, recursive_flags, field_types, _indices))| {
                    let rhs = self.build_recursor_rule_rhs(
                        &rec_name,
                        &rec_level_params,
                        decl.num_params,
                        num_motives,
                        *num_fields,
                        recursive_flags,
                        field_types,
                        total_minors,
                        minor_idx_offset + idx,
                        &rec_ty,
                        &decl.types,
                    );
                    RecursorRule {
                        constructor_name: ctor_name.clone(),
                        num_fields: *num_fields,
                        recursive_fields: recursive_flags.clone(),
                        rhs,
                    }
                },
            )
            .collect();

        // Determine if this type supports K-axiom (UIP) reduction.
        // K-like types have a unique constructor that can be inferred from indices.
        let is_k = self.is_k_like(ind_type, decl.num_params, decl.types.len());

        Ok(RecursorVal {
            name: rec_name,
            arg_order: RecursorArgOrder::MajorAfterMinors,
            level_params: rec_level_params,
            type_: rec_ty,
            inductive_name: ind_name.clone(),
            num_params: decl.num_params,
            num_indices,
            num_motives,
            num_minors: Self::usize_to_u32(total_minors),
            rules,
            is_k,
        })
    }

    /// Build the bespoke **prop-restricted recursor** for the propositional
    /// truncation HIT `∥A∥` (the second known-sound HIT — caller guarantees the
    /// shape via [`crate::inductive::is_prop_truncation_shape`]).
    ///
    /// ```text
    /// ∥A∥.rec : {A : Sort s} → {P : Sort u} → isProp P → (A → P) → ∥A∥ A → P
    ///   ∥A∥.rec A P pP f (∥A∥.in a)        ↝ f a
    ///   ∥A∥.rec A P pP f (∥A∥.squash x y @ i) ↝ pP (rec … x) (rec … y) @ i
    /// ```
    ///
    /// where `isProp P := (x y : P) → Path (λ_.P) x y`. The point-constructor
    /// iota is the ordinary β-reduction `f a`; the `squash` path-constructor iota
    /// is discharged by the supplied `isProp P` witness `pP` (so the result is a
    /// path `rec…x ⇝ rec…y` in `P`), and it is **boundary-coherent**: at `i = i0`
    /// the path collapses to its left endpoint `rec…x`, matching `squash x y @ i0
    /// ↝ x` (and dually at `i1`).
    ///
    /// SOUNDNESS: this is the *standard* non-dependent eliminator of propositional
    /// truncation. The `isProp P` premise is what makes elimination into `P`
    /// sound (without it one could project `A` out of `∥A∥`); both iota rules are
    /// type-preserving (`f a : P`; `pP (rec…x)(rec…y) @ i : P`) and the squash
    /// rule is boundary-coherent. `noConfusion` / `below` / `casesOn` / `recOn`
    /// are deliberately NOT generated — constructor injectivity and structural
    /// recursion are invalid for a path constructor.
    pub(crate) fn build_truncation_recursor(
        &self,
        ind_type: &InductiveType,
        decl: &InductiveDecl,
    ) -> Result<RecursorVal, EnvError> {
        let ind_name = &ind_type.name;
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

        // Parameter domain `A : a_dom`, read verbatim from the type former
        // `Π (A : a_dom). Sort _` (shape-guaranteed by the caller).
        let a_dom = match &ind_type.type_.kind {
            ExprKind::Pi(_, dom, _) => (**dom).clone(),
            _ => {
                return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                    "{ind_name}: prop-truncation recursor requires a `Π (A:Sort). Sort` former"
                ))))
            }
        };

        // Motive universe parameter `u` (P : Sort u), prepended to the inductive's
        // own level params (`∥_∥` is typically monomorphic, so just `[u]`).
        let u = fresh_univ_name(&decl.level_params);
        let mut level_params = vec![u.clone()];
        level_params.extend(decl.level_params.clone());
        let sort_u = Expr::sort(Level::param(u));

        // `∥_∥` applied to its own level params (none, for a monomorphic truncation).
        let ind_levels: Vec<Level> = decl
            .level_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();
        let trunc = Expr::const_(ind_name.clone(), ind_levels);

        // ── Recursor type ──────────────────────────────────────────────────────
        // {A : a_dom} {P : Sort u} (pP : isProp P) (f : A → P) (major : ∥A∥ A) → P
        // De Bruijn at result depth [A,P,pP,f,major]: major=0, f=1, pP=2, P=3, A=4.
        let result = Expr::bvar(3); // P
        let major_dom = Expr::app(trunc.clone(), Expr::bvar(3)); // ∥A∥ A (A=BVar3 here)
        let mut rec_ty = Expr::pi(BinderInfo::Default, major_dom, result);
        // f : A → P  (depth [A,P,pP]: A=BVar2, P=BVar1; arrow lifts cod → BVar2)
        rec_ty = Expr::pi(
            BinderInfo::Default,
            Expr::arrow(Expr::bvar(2), Expr::bvar(2)),
            rec_ty,
        );
        // pP : isProp P  (depth [A,P]: P=BVar0)
        rec_ty = Expr::pi(BinderInfo::Default, is_prop_type(&Expr::bvar(0)), rec_ty);
        // {P : Sort u}
        rec_ty = Expr::pi(BinderInfo::Implicit, sort_u.clone(), rec_ty);
        // {A : a_dom}
        rec_ty = Expr::pi(BinderInfo::Implicit, a_dom.clone(), rec_ty);

        // ── Point-constructor rule: λ A P pP f a. f a ──────────────────────────
        // Depth [A,P,pP,f,a]: a=0, f=1, pP=2, P=3, A=4.
        let in_body = Expr::app(Expr::bvar(1), Expr::bvar(0)); // f a
        let mut in_rhs = Expr::lam(BinderInfo::Default, Expr::bvar(3), in_body); // a : A (BVar3)
        in_rhs = Expr::lam(
            BinderInfo::Default,
            Expr::arrow(Expr::bvar(2), Expr::bvar(2)),
            in_rhs,
        ); // f
        in_rhs = Expr::lam(BinderInfo::Default, is_prop_type(&Expr::bvar(0)), in_rhs); // pP
        in_rhs = Expr::lam(BinderInfo::Default, sort_u.clone(), in_rhs); // P
        in_rhs = Expr::lam(BinderInfo::Default, a_dom.clone(), in_rhs); // A

        // ── Squash rule: λ A P pP f x y. pP (rec A P pP f x) (rec A P pP f y) ───
        // Depth [A,P,pP,f,x,y]: y=0, x=1, f=2, pP=3, P=4, A=5. The `@ i` is
        // re-applied by `try_iota_reduction` (HIT path-constructor iota).
        let rec_levels: Vec<Level> = level_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();
        let rec_const = Expr::const_(rec_name.clone(), rec_levels);
        let rec_at = |arg: Expr| {
            Expr::apps(
                rec_const.clone(),
                [
                    Expr::bvar(5),
                    Expr::bvar(4),
                    Expr::bvar(3),
                    Expr::bvar(2),
                    arg,
                ],
            )
        };
        let sq_body = Expr::apps(
            Expr::bvar(3), // pP
            [rec_at(Expr::bvar(1)), rec_at(Expr::bvar(0))],
        );
        // y : ∥A∥ A (A=BVar4 at depth [A,P,pP,f,x])
        let mut sq_rhs = Expr::lam(
            BinderInfo::Default,
            Expr::app(trunc.clone(), Expr::bvar(4)),
            sq_body,
        );
        // x : ∥A∥ A (A=BVar3 at depth [A,P,pP,f])
        sq_rhs = Expr::lam(
            BinderInfo::Default,
            Expr::app(trunc.clone(), Expr::bvar(3)),
            sq_rhs,
        );
        sq_rhs = Expr::lam(
            BinderInfo::Default,
            Expr::arrow(Expr::bvar(2), Expr::bvar(2)),
            sq_rhs,
        ); // f
        sq_rhs = Expr::lam(BinderInfo::Default, is_prop_type(&Expr::bvar(0)), sq_rhs); // pP
        sq_rhs = Expr::lam(BinderInfo::Default, sort_u, sq_rhs); // P
        sq_rhs = Expr::lam(BinderInfo::Default, a_dom, sq_rhs); // A

        let in_rule = RecursorRule {
            constructor_name: ind_type.constructors[0].name.clone(),
            num_fields: 1,
            recursive_fields: vec![false],
            rhs: in_rhs,
        };
        let squash_rule = RecursorRule {
            constructor_name: ind_type.constructors[1].name.clone(),
            num_fields: 2,
            // The RHS carries explicit recursive `rec` calls; no auto-generated
            // induction hypotheses are needed (and none are read at reduction).
            recursive_fields: vec![false, false],
            rhs: sq_rhs,
        };

        Ok(RecursorVal {
            name: rec_name,
            arg_order: RecursorArgOrder::MajorAfterMinors,
            level_params,
            type_: rec_ty,
            inductive_name: ind_name.clone(),
            num_params: 1, // A
            num_indices: 0,
            num_motives: 1, // P (the constant motive)
            num_minors: 2,  // pP, f
            rules: vec![in_rule, squash_rule],
            is_k: false,
        })
    }

    /// Build the bespoke **dependent recursor** for the suspension HIT `Susp A`
    /// (the third known-sound HIT — caller guarantees the shape via
    /// [`crate::inductive::is_suspension_shape`]).
    ///
    /// ```text
    /// Susp.rec : {A : Sort _} → {C : Susp A → Sort u}
    ///   → (cn : C (north A))
    ///   → (cs : C (south A))
    ///   → (cm : (a : A) → PathP (λ i. C (merid A a @ i)) cn cs)
    ///   → (x : Susp A) → C x
    ///
    ///   Susp.rec … (north A)        ↝ cn
    ///   Susp.rec … (south A)        ↝ cs
    ///   Susp.rec … (merid A a @ r)  ↝ (cm a) @ r
    /// ```
    ///
    /// This is the *standard* dependent eliminator of the suspension. It is built
    /// by hand (rather than via the generic schema) because the `merid` minor
    /// premise is a **path family** `(a : A) → PathP … cn cs` whose endpoints are
    /// the *earlier* point-constructor minors `cn`/`cs` and whose line mentions
    /// the field `a` — more De Bruijn-intricate than the generic path-minor
    /// builder (tuned for S¹'s field-less `loop`) expresses.
    ///
    /// SOUNDNESS:
    /// - The recursor TYPE is the intended dependent eliminator (verified by the
    ///   `is_def_eq`-against-a-hand-built-eliminator test, the S¹ soundness check).
    /// - All three iota rules fire through the **existing** HIT path-constructor
    ///   iota machinery (`try_iota_reduction`), with NO new reduction code:
    ///   * `north`/`south` are ordinary point-constructor rules (`↝ cn` / `↝ cs`).
    ///   * `merid`'s rule RHS is `λ A C cn cs cm a. cm a`, so for a path-applied
    ///     major `(merid A a) @ r` the path-ctor iota produces `(cm a) @ r`, which
    ///     is type-preserving (`cm a : PathP (λ i. C (merid A a @ i)) cn cs`, so
    ///     `(cm a) @ r : C (merid A a @ r)` = `C major`).
    /// - **Boundary coherence:** `(merid A a) @ i0 ↝ north A` (point-endpoint
    ///   reduction), and `(cm a) @ i0 ↝ cn` (PathP endpoint), so the merid rule at
    ///   `i0` agrees with the `north` rule (`↝ cn`); dually at `i1` (`↝ cs`).
    /// - `noConfusion` / `below` / `casesOn` / `recOn` are deliberately NOT
    ///   generated — constructor injectivity and structural recursion are invalid
    ///   for a path constructor (SOUNDNESS-CRITICAL; the caller skips them).
    pub(crate) fn build_suspension_recursor(
        &self,
        ind_type: &InductiveType,
        decl: &InductiveDecl,
    ) -> Result<RecursorVal, EnvError> {
        let ind_name = &ind_type.name;
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));

        // Constructor names, read positionally from the shape-guaranteed decl:
        // [0] = north, [1] = south, [2] = merid.
        let north_name = ind_type
            .constructors
            .first()
            .map(|c| c.name.clone())
            .ok_or_else(|| {
                EnvError::Inductive(InductiveError::InvalidType(format!(
                    "{ind_name}: suspension recursor requires a `north` constructor"
                )))
            })?;
        let south_name = ind_type
            .constructors
            .get(1)
            .map(|c| c.name.clone())
            .ok_or_else(|| {
                EnvError::Inductive(InductiveError::InvalidType(format!(
                    "{ind_name}: suspension recursor requires a `south` constructor"
                )))
            })?;
        let merid_name = ind_type
            .constructors
            .get(2)
            .map(|c| c.name.clone())
            .ok_or_else(|| {
                EnvError::Inductive(InductiveError::InvalidType(format!(
                    "{ind_name}: suspension recursor requires a `merid` constructor"
                )))
            })?;

        // Parameter domain `A : a_dom`, read verbatim from the type former
        // `Π (A : a_dom). Sort _` (shape-guaranteed by the caller).
        let a_dom = match &ind_type.type_.kind {
            ExprKind::Pi(_, dom, _) => (**dom).clone(),
            _ => {
                return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                    "{ind_name}: suspension recursor requires a `Π (A:Sort). Sort` former"
                ))))
            }
        };

        // Motive universe parameter `u` (C : Susp A → Sort u), prepended to the
        // inductive's own level params (`Susp` is typically monomorphic, so `[u]`).
        let u = fresh_univ_name(&decl.level_params);
        let mut level_params = vec![u.clone()];
        level_params.extend(decl.level_params.clone());
        let sort_u = Expr::sort(Level::param(u));

        // Constructors share the inductive's level params (empty for monomorphic
        // `Susp`). Closures build `Susp a`, `north a`, `south a`, `merid a₀ a₁`.
        let ind_levels: Vec<Level> = decl
            .level_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();
        let susp = {
            let lv = ind_levels.clone();
            let n = ind_name.clone();
            move |a: Expr| Expr::app(Expr::const_(n.clone(), lv.clone()), a)
        };
        let north = {
            let lv = ind_levels.clone();
            let n = north_name.clone();
            move |a: Expr| Expr::app(Expr::const_(n.clone(), lv.clone()), a)
        };
        let south = {
            let lv = ind_levels.clone();
            let n = south_name.clone();
            move |a: Expr| Expr::app(Expr::const_(n.clone(), lv.clone()), a)
        };
        let merid = {
            let lv = ind_levels.clone();
            let n = merid_name.clone();
            move |a_param: Expr, a_field: Expr| {
                Expr::apps(Expr::const_(n.clone(), lv.clone()), [a_param, a_field])
            }
        };
        let path_app = |path: Expr, arg: Expr| {
            Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(path),
                arg: Arc::new(arg),
            })
        };
        let interval = || Expr::from_kind(ExprKind::CubicalInterval);

        // ── Shared binder DOMAINS (telescope [A, C, cn, cs, cm, x]) ─────────────
        // Each domain is written in the context *outside* its own binder.

        // C : Susp A → Sort u            (context [A]: A = BVar0)
        let c_dom = Expr::pi(BinderInfo::Default, susp(Expr::bvar(0)), sort_u.clone());

        // cn : C (north A)               (context [A, C]: C = BVar0, A = BVar1)
        let cn_dom = Expr::app(Expr::bvar(0), north(Expr::bvar(1)));

        // cs : C (south A)               (context [A, C, cn]: C = BVar1, A = BVar2)
        let cs_dom = Expr::app(Expr::bvar(1), south(Expr::bvar(2)));

        // cm : (a : A) → PathP (λ i. C (merid A a @ i)) cn cs
        //   context [A, C, cn, cs]: cs=0, cn=1, C=2, A=3
        //   under a   [A, C, cn, cs, a]: a=0, cs=1, cn=2, C=3, A=4
        //   under λ i [A, C, cn, cs, a, i]: i=0, a=1, cs=2, cn=3, C=4, A=5
        let cm_line_body = Expr::app(
            Expr::bvar(4),                                                // C
            path_app(merid(Expr::bvar(5), Expr::bvar(1)), Expr::bvar(0)), // (merid A a) @ i
        );
        let cm_line = Expr::lam(BinderInfo::Default, interval(), cm_line_body);
        let cm_pathp = Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(cm_line),
            left: Arc::new(Expr::bvar(2)),  // cn
            right: Arc::new(Expr::bvar(1)), // cs
        });
        let cm_dom = Expr::pi(BinderInfo::Default, Expr::bvar(3) /* A */, cm_pathp);

        // ── Recursor TYPE (inside-out) ─────────────────────────────────────────
        // {A} {C} (cn) (cs) (cm) (x : Susp A) → C x
        // result body: C x   (context [A,C,cn,cs,cm,x]: C=4, x=0)
        let mut rec_ty = Expr::app(Expr::bvar(4), Expr::bvar(0));
        // (x : Susp A)        (context [A,C,cn,cs,cm]: A=4)
        rec_ty = Expr::pi(BinderInfo::Default, susp(Expr::bvar(4)), rec_ty);
        // (cm : …)
        rec_ty = Expr::pi(BinderInfo::Default, cm_dom.clone(), rec_ty);
        // (cs : C (south A))
        rec_ty = Expr::pi(BinderInfo::Default, cs_dom.clone(), rec_ty);
        // (cn : C (north A))
        rec_ty = Expr::pi(BinderInfo::Default, cn_dom.clone(), rec_ty);
        // {C : Susp A → Sort u}
        rec_ty = Expr::pi(BinderInfo::Implicit, c_dom.clone(), rec_ty);
        // {A : a_dom}
        rec_ty = Expr::pi(BinderInfo::Implicit, a_dom.clone(), rec_ty);

        // ── Rule RHSs ──────────────────────────────────────────────────────────
        // The lambda telescope's binder DOMAINS are irrelevant to reduction (they
        // are beta-stripped when params+motives+minors+fields are applied); we
        // reuse the recursor's own domains for clarity. The BODY's BVars are what
        // matters.

        // λ A C cn cs cm. cn   — north rule (point ctor, 0 fields).
        // body cn at context [A,C,cn,cs,cm]: cn = BVar2.
        let mut north_rhs = Expr::bvar(2);
        north_rhs = Expr::lam(BinderInfo::Default, cm_dom.clone(), north_rhs);
        north_rhs = Expr::lam(BinderInfo::Default, cs_dom.clone(), north_rhs);
        north_rhs = Expr::lam(BinderInfo::Default, cn_dom.clone(), north_rhs);
        north_rhs = Expr::lam(BinderInfo::Default, c_dom.clone(), north_rhs);
        north_rhs = Expr::lam(BinderInfo::Default, a_dom.clone(), north_rhs);

        // λ A C cn cs cm. cs   — south rule (point ctor, 0 fields).
        // body cs at context [A,C,cn,cs,cm]: cs = BVar1.
        let mut south_rhs = Expr::bvar(1);
        south_rhs = Expr::lam(BinderInfo::Default, cm_dom.clone(), south_rhs);
        south_rhs = Expr::lam(BinderInfo::Default, cs_dom.clone(), south_rhs);
        south_rhs = Expr::lam(BinderInfo::Default, cn_dom.clone(), south_rhs);
        south_rhs = Expr::lam(BinderInfo::Default, c_dom.clone(), south_rhs);
        south_rhs = Expr::lam(BinderInfo::Default, a_dom.clone(), south_rhs);

        // λ A C cn cs cm a. cm a   — merid rule (path ctor, 1 field).
        // body `cm a` at context [A,C,cn,cs,cm,a]: cm = BVar1, a = BVar0.
        // The `@ r` is re-applied by `try_iota_reduction` (HIT path-ctor iota).
        let mut merid_rhs = Expr::app(Expr::bvar(1), Expr::bvar(0));
        // λ a : A   (A at context [A,C,cn,cs,cm] = BVar4)
        merid_rhs = Expr::lam(BinderInfo::Default, Expr::bvar(4), merid_rhs);
        merid_rhs = Expr::lam(BinderInfo::Default, cm_dom, merid_rhs);
        merid_rhs = Expr::lam(BinderInfo::Default, cs_dom, merid_rhs);
        merid_rhs = Expr::lam(BinderInfo::Default, cn_dom, merid_rhs);
        merid_rhs = Expr::lam(BinderInfo::Default, c_dom, merid_rhs);
        merid_rhs = Expr::lam(BinderInfo::Default, a_dom, merid_rhs);

        let north_rule = RecursorRule {
            constructor_name: north_name,
            num_fields: 0,
            recursive_fields: vec![],
            rhs: north_rhs,
        };
        let south_rule = RecursorRule {
            constructor_name: south_name,
            num_fields: 0,
            recursive_fields: vec![],
            rhs: south_rhs,
        };
        let merid_rule = RecursorRule {
            constructor_name: merid_name,
            num_fields: 1,
            recursive_fields: vec![false],
            rhs: merid_rhs,
        };

        Ok(RecursorVal {
            name: rec_name,
            arg_order: RecursorArgOrder::MajorAfterMinors,
            level_params,
            type_: rec_ty,
            inductive_name: ind_name.clone(),
            num_params: 1, // A
            num_indices: 0,
            num_motives: 1, // C (the dependent motive)
            num_minors: 3,  // cn, cs, cm
            rules: vec![north_rule, south_rule, merid_rule],
            is_k: false,
        })
    }

    /// Build casesOn (non-recursive eliminator) for an inductive type.
    ///
    /// Similar to `build_recursor` but without induction hypotheses.
    /// For mutual inductives, includes all motives and all minors like build_recursor.
    pub(crate) fn build_cases_on(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        ctor_infos: &[CtorInfo],
        all_ctor_infos: &[CtorInfo],
        minor_idx_offset: usize,
    ) -> Result<RecursorVal, EnvError> {
        let ind_type = decl
            .types
            .iter()
            .find(|t| &t.name == ind_name)
            .ok_or_else(|| EnvError::UnknownInductive(ind_name.clone()))?;

        let cases_name = Name::from_string(&format!("{ind_name}.casesOn"));

        // Lean 4: Prop-only elimination → no extra motive universe param.
        let prop_only = elim_only_at_universe_zero(
            self,
            &ind_type.type_,
            &ind_type.constructors,
            decl.num_params,
            decl.types.len(),
        );

        let (motive_univ_name_opt, cases_level_params) = if prop_only {
            (None, decl.level_params.clone())
        } else {
            let motive_univ_name = fresh_univ_name(&decl.level_params);
            let mut params = vec![motive_univ_name.clone()];
            params.extend(decl.level_params.clone());
            (Some(motive_univ_name), params)
        };

        let type_arity = count_pi_args(&ind_type.type_);
        let num_indices = type_arity.saturating_sub(decl.num_params);

        let num_motives = decl.types.len() as u32;

        // For casesOn, override recursive_flags to all-false (no IH parameters)
        // for ALL constructor infos.
        let cases_all_ctor_infos: Vec<CtorInfo> = all_ctor_infos
            .iter()
            .map(
                |(name, num_fields, _recursive_flags, field_types, return_indices)| {
                    (
                        name.clone(),
                        *num_fields,
                        vec![false; *num_fields as usize],
                        field_types.clone(),
                        return_indices.clone(),
                    )
                },
            )
            .collect();

        let total_minors = cases_all_ctor_infos.len();

        // Rec-layout twin (params → motives → minors → indices → major) used
        // ONLY for rule-RHS construction: `build_recursor_rule_rhs` reads its
        // binder domains positionally in canonical rec order.
        let cases_rhs_ty = self.build_recursor_type(
            ind_name,
            &ind_type.type_,
            decl.num_params,
            num_indices,
            motive_univ_name_opt.as_ref(),
            &decl.level_params,
            &cases_all_ctor_infos,
            &decl.types,
        );

        // The stored casesOn type is Lean-faithful: params → motives →
        // indices → major → minors (the recOn binder layout, with no-IH minor
        // premises). Lean 4 generates casesOn with the major premise BEFORE
        // the minors (Lean/Meta/Constructions/CasesOn.lean); spelling it
        // rec-style made every `.olean`-elaborated casesOn application
        // mis-typecheck against Clean-regenerated environments (the major
        // premise landed in the first minor slot).
        let cases_ty = self.build_rec_on_type(
            ind_name,
            &ind_type.type_,
            decl.num_params,
            num_indices,
            motive_univ_name_opt.as_ref(),
            &decl.level_params,
            &cases_all_ctor_infos,
            &decl.types,
        );

        // Build casesOn rules for THIS type's constructors only.
        // casesOn minor premises have no IH (recursive_flags all false).
        let cases_this_type_infos: Vec<CtorInfo> = ctor_infos
            .iter()
            .map(
                |(name, num_fields, _recursive_flags, field_types, return_indices)| {
                    (
                        name.clone(),
                        *num_fields,
                        vec![false; *num_fields as usize],
                        field_types.clone(),
                        return_indices.clone(),
                    )
                },
            )
            .collect();
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));
        let rules: Vec<RecursorRule> = cases_this_type_infos
            .iter()
            .enumerate()
            .map(
                |(idx, (ctor_name, num_fields, recursive_flags, field_types, _indices))| {
                    let rhs = self.build_recursor_rule_rhs(
                        &rec_name,
                        &cases_level_params,
                        decl.num_params,
                        num_motives,
                        *num_fields,
                        recursive_flags,
                        field_types,
                        total_minors,
                        minor_idx_offset + idx,
                        &cases_rhs_ty,
                        &decl.types,
                    );
                    RecursorRule {
                        constructor_name: ctor_name.clone(),
                        num_fields: *num_fields,
                        recursive_fields: recursive_flags.clone(),
                        rhs,
                    }
                },
            )
            .collect();

        // K-axiom applies to casesOn as well
        let is_k = self.is_k_like(ind_type, decl.num_params, decl.types.len());

        Ok(RecursorVal {
            name: cases_name,
            arg_order: RecursorArgOrder::MajorAfterMotive,
            level_params: cases_level_params,
            type_: cases_ty,
            inductive_name: ind_name.clone(),
            num_params: decl.num_params,
            num_indices,
            num_motives,
            num_minors: Self::usize_to_u32(total_minors),
            rules,
            is_k,
        })
    }

    /// Build recOn (recursor with major premise first) for an inductive type.
    ///
    /// For mutual inductives, includes all motives and all minors like build_recursor.
    pub(crate) fn build_rec_on(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        ctor_infos: &[CtorInfo],
        all_ctor_infos: &[CtorInfo],
        minor_idx_offset: usize,
    ) -> Result<RecursorVal, EnvError> {
        let ind_type = decl
            .types
            .iter()
            .find(|t| &t.name == ind_name)
            .ok_or_else(|| EnvError::UnknownInductive(ind_name.clone()))?;

        let rec_on_name = Name::from_string(&format!("{ind_name}.recOn"));

        // Lean 4: Prop-only elimination → no extra motive universe param.
        let prop_only = elim_only_at_universe_zero(
            self,
            &ind_type.type_,
            &ind_type.constructors,
            decl.num_params,
            decl.types.len(),
        );

        let (motive_univ_name_opt, rec_on_level_params) = if prop_only {
            (None, decl.level_params.clone())
        } else {
            let motive_univ_name = fresh_univ_name(&decl.level_params);
            let mut params = vec![motive_univ_name.clone()];
            params.extend(decl.level_params.clone());
            (Some(motive_univ_name), params)
        };

        let type_arity = count_pi_args(&ind_type.type_);
        let num_indices = type_arity.saturating_sub(decl.num_params);

        let num_motives = decl.types.len() as u32;
        let total_minors = all_ctor_infos.len();

        // Build recOn type (motives → major → minors → motive major)
        let rec_on_ty = self.build_rec_on_type(
            ind_name,
            &ind_type.type_,
            decl.num_params,
            num_indices,
            motive_univ_name_opt.as_ref(),
            &decl.level_params,
            all_ctor_infos,
            &decl.types,
        );

        // Build recOn rules. The RHS lambda has the same structure as the standard rec
        // RHS — λ params motives minors fields. minor fields... IH... — because
        // try_iota_reduction normalizes argument gathering before application.
        let rec_name = Name::from_string(&format!("{ind_name}.rec"));
        let std_rec_ty = self
            .recursors
            .get(&rec_name)
            .expect("rec must be registered before recOn")
            .type_
            .clone();
        // Build recOn rules for THIS type's constructors only.
        let rules: Vec<RecursorRule> = ctor_infos
            .iter()
            .enumerate()
            .map(
                |(idx, (ctor_name, num_fields, recursive_flags, field_types, _indices))| {
                    let rhs = self.build_recursor_rule_rhs(
                        &rec_name,
                        &rec_on_level_params,
                        decl.num_params,
                        num_motives,
                        *num_fields,
                        recursive_flags,
                        field_types,
                        total_minors,
                        minor_idx_offset + idx,
                        &std_rec_ty,
                        &decl.types,
                    );
                    RecursorRule {
                        constructor_name: ctor_name.clone(),
                        num_fields: *num_fields,
                        recursive_fields: recursive_flags.clone(),
                        rhs,
                    }
                },
            )
            .collect();

        // K-axiom applies to recOn as well
        let is_k = self.is_k_like(ind_type, decl.num_params, decl.types.len());

        Ok(RecursorVal {
            name: rec_on_name,
            arg_order: RecursorArgOrder::MajorAfterMotive,
            level_params: rec_on_level_params,
            type_: rec_on_ty,
            inductive_name: ind_name.clone(),
            num_params: decl.num_params,
            num_indices,
            num_motives,
            num_minors: Self::usize_to_u32(total_minors),
            rules,
            is_k,
        })
    }

    /// Get flags indicating which constructor fields are recursive
    ///
    /// For mutual inductives, a field is recursive if it mentions ANY type in the
    /// mutual block (not just the type being defined). This is essential for proper
    /// mutual recursion support where Even.succ_odd : Odd → Even should have an IH.
    ///
    /// A field counts as *eliminably* recursive only when, after stripping its
    /// Pi binders, the HEAD of its return type is one of the block inductives
    /// (e.g. `Even`, `V._List`). The entire IH machinery — `field_motive_index`,
    /// the minor-premise builder, and the recursor rule RHS — assumes the IH
    /// motive/recursor can be read off that head. A field whose head is NOT a
    /// block type but which merely *mentions* one as a strict argument (e.g.
    /// `Prod String V` left behind by single-level nested elimination of
    /// `List (Prod String V)`) is a non-eliminable nested occurrence: clean does
    /// not synthesise a second-level aux for it, so no structural IH exists.
    /// Flagging it recursive would emit an ill-typed IH (`motive String V x`,
    /// applying a unary motive to the container's arguments) and a `Prod.rec`
    /// rule RHS. We therefore treat such fields as non-recursive (no IH), which
    /// yields a sound — if weaker — recursor whose type the kernel accepts. This
    /// is faithful to Lean's behaviour for nesting it cannot see through.
    fn get_recursive_field_flags(
        &self,
        ctor_ty: &Expr,
        ind_name_set: &std::collections::HashSet<&Name>,
        num_params: u32,
    ) -> Vec<bool> {
        let mut flags = Vec::new();
        let mut current = ctor_ty.clone();
        let mut arg_count = 0u32;

        while let ExprKind::Pi(_, domain, codomain) = &current.kind {
            if arg_count >= num_params {
                flags.push(Self::field_is_eliminably_recursive(domain, ind_name_set));
            }
            current = (**codomain).clone();
            arg_count += 1;
        }
        flags
    }

    /// A field is *eliminably* recursive iff, after stripping all leading Pi
    /// binders (so reflexive fields like `Unit -> Even` are handled), the head
    /// of its return type is one of the block inductives. Strict-argument-only
    /// occurrences (`Prod String V`, `List (Prod String V)` before its outer
    /// container is eliminated) return `false` — see `get_recursive_field_flags`.
    fn field_is_eliminably_recursive(
        field_ty: &Expr,
        ind_name_set: &std::collections::HashSet<&Name>,
    ) -> bool {
        let ret_ty = get_return_type(field_ty);
        let head = ret_ty.get_app_fn();
        matches!(&head.kind, ExprKind::Const(name, _) if ind_name_set.contains(name))
    }

    /// Get the types of constructor fields (after skipping parameters)
    ///
    /// For `cons : MyNat → MyList → MyList` with num_params=0, returns [MyNat, MyList].
    /// For `cons : {A : Type} → A → List A → List A` with num_params=1, returns [A, List A].
    pub(crate) fn get_constructor_field_types(&self, ctor_ty: &Expr, num_params: u32) -> Vec<Expr> {
        let mut types = Vec::new();
        let mut current = ctor_ty.clone();
        let mut arg_count = 0u32;

        while let ExprKind::Pi(_, domain, codomain) = &current.kind {
            if arg_count >= num_params {
                // Lean kernel parity: every binder domain the inductive
                // machinery collects is stripped of elaborator gadgets
                // (`optParam` / `autoParam` / `outParam` / `semiOutParam`)
                // via `consume_type_annotations`, so generated recursor
                // minor premises match Lean's spelling exactly (e.g.
                // `Lean.SourceInfo.synthetic`'s defaulted `Bool` field).
                types.push(consume_type_annotations(domain).clone());
            }
            current = (**codomain).clone();
            arg_count += 1;
        }
        types
    }

    /// Get the return indices from a constructor type.
    ///
    /// For `Eq.refl : ∀ {α : Sort u} (a : α), Eq α a a` with num_params=1,
    /// the return type is `Eq α a a` and indices are `[a, a]` (the second and third args).
    ///
    /// For a constructor returning `Ind p₁ ... pₙ i₁ ... iₘ`, we skip the first
    /// num_params applications (parameters) and return the remaining index arguments.
    ///
    /// # Contract
    ///
    /// REQUIRES: `ctor_ty` is a well-formed constructor type (Pi chain ending in application)
    /// REQUIRES: `num_params` <= number of applications in return type
    ///
    /// ENSURES: Returns index expressions from constructor return type (after parameters)
    /// ENSURES: Result length = number of indices in the inductive type
    pub(crate) fn get_constructor_return_indices(
        &self,
        ctor_ty: &Expr,
        num_params: u32,
    ) -> Vec<Expr> {
        // Navigate past all Pi binders to get the return type
        let mut current = ctor_ty.clone();
        while let ExprKind::Pi(_, _, codomain) = &current.kind {
            current = (**codomain).clone();
        }

        // current is now something like: Ind p₁ ... pₙ i₁ ... iₘ
        // Collect all the arguments
        let mut args: Vec<Expr> = Vec::new();
        while let ExprKind::App(f, a) = &current.kind {
            args.push((**a).clone());
            current = (**f).clone();
        }
        // Arguments are collected in reverse order (rightmost first)
        args.reverse();

        // Skip the first num_params arguments (parameters) and return the rest (indices)
        args.into_iter().skip(num_params as usize).collect()
    }

    /// Collect binder info and types from a Pi chain.
    ///
    /// For `∀ (a : α) {b : β}, γ` with count=2, returns:
    /// `[(Default, α), (Implicit, β)]`
    ///
    /// # Contract
    ///
    /// REQUIRES: `ty` is well-formed
    /// REQUIRES: `count` <= number of Pi binders in `ty`
    ///
    /// ENSURES: Returns `count` binder info/type pairs in order
    /// ENSURES: If `ty` has fewer than `count` Pi binders, returns available binders
    pub(crate) fn collect_pi_binders(&self, ty: &Expr, count: u32) -> Vec<(BinderData, Expr)> {
        let mut result = Vec::new();
        let mut current = ty.clone();
        let mut collected = 0u32;

        while collected < count {
            if let ExprKind::Pi(bi, domain, codomain) = &current.kind {
                // Lean kernel parity: binder domains are collected through
                // `consume_type_annotations` (see
                // `inductive::consume_type_annotations`).
                result.push((*bi, consume_type_annotations(domain).clone()));
                current = (**codomain).clone();
                collected += 1;
            } else {
                break;
            }
        }
        result
    }

    /// Check if an inductive type supports K-axiom (UIP) reduction.
    ///
    /// Per Lean 4 (kernel/inductive.cpp:init_K_target, lines 551-572), a type
    /// supports K-like reduction if ALL of:
    /// 1. It is NOT a mutual declaration (single inductive type)
    /// 2. It is an inductive predicate (result type is Prop, i.e., `Sort 0`)
    /// 3. It has exactly one constructor
    /// 4. The constructor has no real fields after parameters (nullary after
    ///    fixed-index promotion)
    ///
    /// Lean 4 runs `fixedIndicesToParams` before `init_K_target`, promoting
    /// constructor arguments that fill index positions to parameters. clean
    /// now runs `fixed_indices_to_params` before `is_k_like` in `add_inductive`,
    /// so `num_params` is already promoted when this function is called.
    /// After promotion, K-like types have `num_ctor_args == 0` (all extra args
    /// became parameters). A defensive fallback check remains for any edge
    /// case where promotion doesn't fully apply.
    ///
    /// For K-like types, the kernel can reduce any proof `e : I a a` to the
    /// unique constructor when the indices are definitionally equal. This enables
    /// UIP (uniqueness of identity proofs) for types like `Eq`.
    ///
    /// Examples:
    /// - `True` is K-like: Prop, one ctor `True.intro`, 0 fields (matches Lean 4)
    /// - `Eq` is K-like: Prop, one ctor `Eq.refl`, `a` fills indices
    /// - `HEq` is K-like: Prop, one ctor `HEq.refl`, `a` fills indices
    /// - `Nat` is NOT K-like: not in Prop (it's in `Type`)
    /// - `List` is NOT K-like: not in Prop
    /// - `Or` is NOT K-like: has two constructors
    /// - Phantom args NOT K-like: `mk : Nat → Bad4 0` — phantom doesn't fill index
    /// - Mutual inductives NOT K-like: even if one type qualifies individually
    fn is_k_like(&self, ind_type: &InductiveType, num_params: u32, num_types: usize) -> bool {
        // K requires a non-mutual declaration (Lean 4 inductive.cpp:555)
        if num_types != 1 {
            return false;
        }

        // K requires exactly one constructor
        if ind_type.constructors.len() != 1 {
            return false;
        }

        // K requires the type to be in Prop (Sort 0).
        let result_type = get_return_type(&ind_type.type_);
        let is_prop = match &result_type.kind {
            ExprKind::Sort(level) => level.is_zero(),
            _ => false,
        };
        if !is_prop {
            return false;
        }

        let ctor = &ind_type.constructors[0];
        let ctor_arity = count_pi_args(&ctor.type_);

        // Number of constructor arguments after parameters
        let num_ctor_args = ctor_arity.saturating_sub(num_params);

        // Get the inductive type's arity to determine num_indices
        let type_arity = count_pi_args(&ind_type.type_);
        let num_indices = type_arity.saturating_sub(num_params);

        // Lean 4's init_K_target (inductive.cpp:551-573) requires the constructor
        // to have exactly zero fields after parameters. Since fixed_indices_to_params
        // now runs before is_k_like, num_params is already promoted, so K-like
        // types like Eq will have num_ctor_args == 0 and return true above.
        //
        // Defensive fallback: if any constructor argument beyond num_params
        // doesn't fill its index position as a direct BVar, the type is NOT
        // K-like. This handles edge cases where promotion doesn't fully apply.
        if num_ctor_args == 0 {
            // No extra args beyond params — trivially K-like (matches Lean 4)
            return true;
        }

        // Extract index arguments from the constructor's return type.
        // The return type (under all ctor_arity binders) should be:
        //   IndName param₀ ... paramₖ idx₀ ... idxₘ
        let ctor_return = get_return_type(&ctor.type_);
        let ctor_ret_args = ctor_return.get_app_args();

        // Return type should have num_params + num_indices arguments
        if ctor_ret_args.len() < (num_params as usize + num_indices as usize) {
            return false;
        }

        // Extract just the index arguments (skip the param arguments)
        let index_args = &ctor_ret_args[num_params as usize..];

        // For each constructor argument beyond num_params, check that it
        // fills the corresponding index position (positional check matching
        // Lean 4's computeFixedIndexBitMask: xs[i] == typeArgs[i]).
        for j in num_params..ctor_arity {
            let idx_pos = (j - num_params) as usize;
            if idx_pos >= index_args.len() {
                // More extra args than indices — extra arg is a real field.
                return false;
            }
            // Under ctor_arity binders, argument j is BVar(ctor_arity - 1 - j)
            let expected_bvar = ctor_arity - 1 - j;
            let positional_match =
                matches!(&index_args[idx_pos].kind, ExprKind::BVar(v) if *v == expected_bvar);
            if !positional_match {
                // This constructor argument doesn't fill its corresponding
                // index position — it's a real field. Not K-like.
                return false;
            }
        }

        true
    }

    /// Check if a type mentions any of the given inductive types (by name set).
    ///
    /// This handles mutual inductives where a type may reference other types
    /// in the same mutual block. For example, in Even/Odd mutual inductives,
    /// Even.succ_odd's field type (Odd) should be detected as recursive.
    ///
    /// ENSURES: O(n) where n = expression nodes (uses HashSet for O(1) lookup)
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn type_mentions_any_inductive_impl(
        &self,
        ty: &Expr,
        ind_names: &std::collections::HashSet<&Name>,
    ) -> bool {
        match &ty.kind {
            ExprKind::Const(name, _) => ind_names.contains(name),
            ExprKind::App(f, a) => {
                self.type_mentions_any_inductive_impl(f, ind_names)
                    || self.type_mentions_any_inductive_impl(a, ind_names)
            }
            ExprKind::Pi(_, domain, codomain) => {
                self.type_mentions_any_inductive_impl(domain, ind_names)
                    || self.type_mentions_any_inductive_impl(codomain, ind_names)
            }
            ExprKind::Lam(_, ty_inner, body) => {
                self.type_mentions_any_inductive_impl(ty_inner, ind_names)
                    || self.type_mentions_any_inductive_impl(body, ind_names)
            }
            ExprKind::Let(_, ty_inner, val, body, _) => {
                self.type_mentions_any_inductive_impl(ty_inner, ind_names)
                    || self.type_mentions_any_inductive_impl(val, ind_names)
                    || self.type_mentions_any_inductive_impl(body, ind_names)
            }
            _ => false,
        }
    }
}

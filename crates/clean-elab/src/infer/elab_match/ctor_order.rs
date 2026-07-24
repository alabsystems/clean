// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructor-order lowering helpers for non-recursive `casesOn` matches.

use super::*;

impl<'a> ElabCtx<'a> {
    /// Whether `expr` is *ground*: no free variables, no metavariables, no loose
    /// bound variables. A ground index value can be compared for impossibility by
    /// definitional equality alone — there is nothing left that could later
    /// unify it with a different value.
    fn is_ground_index(expr: &Expr) -> bool {
        !expr.has_fvar_quick() && !expr.has_expr_mvar_quick() && !expr.has_loose_bvars_quick()
    }

    /// The head *constructor* of `expr` (after WHNF) together with the name of
    /// the inductive it belongs to — or `None` when `expr`'s head is not a
    /// registered constructor.
    ///
    /// This is the no-confusion handle: two index values whose heads are
    /// *distinct constructors of the same inductive* can never be definitionally
    /// equal, **regardless of any free variables in their arguments** (Lean's
    /// `noConfusion` / injectivity-of-constructors discipline). That is a strictly
    /// stronger impossibility witness than the ground/def-eq check: `Nat.zero` and
    /// `Nat.succ n` clash even though `Nat.succ n` is non-ground.
    fn index_head_ctor(&self, expr: &Expr) -> Option<(Name, Name)> {
        let whnf = self.whnf(expr);
        match whnf.get_app_fn().kind() {
            ExprKind::Const(name, _) => self
                .env
                .get_constructor(name)
                .map(|info| (name.clone(), info.inductive_name.clone())),
            // A `Nat` literal is *definitionally* its constructor form (per the
            // kernel's `nat_lit_to_constructor`): `0` is `Nat.zero` and any `k > 0`
            // is `Nat.succ (k-1)`. Surface syntax writes GADT indices as numeric
            // literals (`Vec α 0`), so without this the no-confusion handle would
            // miss `Nat.zero`-vs-`Nat.succ n` clashes whenever either side is a
            // literal — exactly the `clean check` divergence from the hand-built
            // `Const("Nat.zero")` form. Recovering the constructor head here keeps
            // the impossibility check sound (it still only reports a clash between
            // *distinct* constructors of the *same* inductive).
            ExprKind::Lit(Literal::Nat(n)) => {
                let nat = Name::from_string("Nat");
                if n.is_zero() {
                    Some((Name::from_string("Nat.zero"), nat))
                } else {
                    Some((Name::from_string("Nat.succ"), nat))
                }
            }
            _ => None,
        }
    }

    /// Whether two index values are provably distinct by a *constructor-head
    /// clash*: both reduce to applications headed by constructors of the **same**
    /// inductive, and those constructors differ.
    ///
    /// SOUNDNESS: distinct constructors of one inductive are disjoint (no value is
    /// built by two different constructors), so no instantiation of any free
    /// variables inside the arguments can ever make the two equal. This holds for
    /// non-ground arguments (`succ n` vs `zero`), which the ground-only def-eq
    /// check cannot decide. It is conservative: when either head is not a
    /// constructor (a variable index, a stuck application, …) it returns `false`.
    fn index_heads_clash(&self, a: &Expr, b: &Expr) -> bool {
        match (self.index_head_ctor(a), self.index_head_ctor(b)) {
            (Some((ca, inda)), Some((cb, indb))) => inda == indb && ca != cb,
            _ => false,
        }
    }

    /// The constructor's own *return-type index arguments*, with the inductive
    /// parameters instantiated from the scrutinee type.
    ///
    /// For a GADT constructor like `litBool : Bool -> GExpr Ty.bool` the return
    /// type is `GExpr Ty.bool`; after stripping the inductive's parameters this
    /// yields the single index argument `[Ty.bool]`. Returns `None` when the
    /// constructor is not registered or its arity does not decompose cleanly.
    fn ctor_return_index_args(
        &mut self,
        ctor_name: &Name,
        scrutinee_ty: &Expr,
    ) -> Option<Vec<Expr>> {
        let info = self.env.get_constructor(ctor_name)?.clone();
        let num_indices = self
            .env
            .get_inductive(&info.inductive_name)
            .map(|ind| ind.num_indices as usize)?;
        let num_params = info.num_params as usize;
        let num_fields = info.num_fields as usize;
        if num_indices == 0 {
            return Some(vec![]);
        }

        let scrutinee_ty = self.metas.instantiate(scrutinee_ty);
        let scrutinee_ty = self.metas.instantiate_levels(&scrutinee_ty);
        let scrutinee_ty = self.whnf(&scrutinee_ty);
        let type_args = self.extract_type_args(&scrutinee_ty, info.num_params);
        let scrutinee_levels = match scrutinee_ty.get_app_fn().kind() {
            ExprKind::Const(_, levels) if levels.len() == info.level_params.len() => Some(
                info.level_params
                    .iter()
                    .cloned()
                    .zip(levels.iter().cloned())
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        };
        let mut ctor_ty = scrutinee_levels.as_ref().map_or_else(
            || info.type_.clone(),
            |subst| info.type_.instantiate_level_params(subst),
        );
        // Instantiate the inductive parameters from the scrutinee.
        for i in 0..num_params {
            if let ExprKind::Pi(_, _, codomain) = ctor_ty.kind() {
                // A constructor parameter must come from the fully applied
                // scrutinee type. Fabricating `Type` here changes the
                // constructor telescope and can make an impossible GADT arm
                // appear viable.
                let arg = type_args.get(i)?.clone();
                ctor_ty = codomain.instantiate(&arg);
            } else {
                return None;
            }
        }
        // Strip the constructor's fields to reach the return type. Each field is
        // bound by a fresh local so that a dependent return index (one that
        // mentions a field) becomes an `FVar` (hence non-ground) rather than a
        // loose `BVar` — keeping such constructors conservatively "possible".
        let mut field_fvars: Vec<FVarId> = Vec::with_capacity(num_fields);
        let mut decompose_ok = true;
        for _ in 0..num_fields {
            if let ExprKind::Pi(_, domain, codomain) = ctor_ty.kind() {
                let dom = Self::open_field_type_with_fvars(domain, &field_fvars);
                let fvar = self.push_local("_idx_field".to_string(), dom);
                field_fvars.push(fvar);
                ctor_ty = codomain.instantiate(&Expr::fvar(fvar));
            } else {
                decompose_ok = false;
                break;
            }
        }
        // The return type is `T params… indices…`; collect its spine and keep the
        // trailing `num_indices` arguments.
        let ret = self.whnf(&ctor_ty);
        // Pop the field locals (LIFO) regardless of whether decomposition
        // succeeded, so the local stack is left exactly as we found it.
        for _ in 0..field_fvars.len() {
            self.pop_local();
        }
        if !decompose_ok {
            return None;
        }
        let mut spine: Vec<Expr> = Vec::new();
        let mut head = &ret;
        while let ExprKind::App(func, arg) = head.kind() {
            spine.push((**arg).clone());
            head = func;
        }
        spine.reverse();
        if spine.len() < num_indices {
            return None;
        }
        Some(spine.split_off(spine.len() - num_indices))
    }

    /// Whether the constructor `ctor_name` is *index-incompatible* with the
    /// scrutinee — i.e. a GADT-impossible branch. This is the index-refinement
    /// check: a match on a value of `T concreteIdx` can never select a
    /// constructor whose own return index is a different concrete value.
    ///
    /// SOUNDNESS: returns `true` only when, for some index position, BOTH the
    /// scrutinee's index and the constructor's return index are *ground* (closed,
    /// no fvars/metavars/loose bvars) and are NOT definitionally equal. When
    /// either side is non-ground (a variable index, a metavariable, …) the two
    /// might still unify, so the constructor is conservatively treated as
    /// possible and this returns `false` — never silently discarding a reachable
    /// branch.
    pub(in crate::infer) fn ctor_index_is_impossible(
        &mut self,
        ctor_name: &Name,
        scrutinee_ty: &Expr,
    ) -> bool {
        let ind_name = match self.env.get_constructor(ctor_name) {
            Some(info) => info.inductive_name.clone(),
            None => return false,
        };
        let ind_info = match self.env.get_inductive(&ind_name) {
            Some(ind) => ind,
            None => return false,
        };
        let num_indices = ind_info.num_indices as usize;
        if num_indices == 0 {
            return false;
        }
        let num_params = ind_info.num_params as usize;

        // Scrutinee index args (params first, then indices).
        let scrutinee_ty_w = self.whnf(
            &self
                .metas
                .instantiate_levels(&self.metas.instantiate(scrutinee_ty)),
        );
        let mut scrut_spine: Vec<Expr> = Vec::new();
        let mut head = &scrutinee_ty_w;
        while let ExprKind::App(func, arg) = head.kind() {
            scrut_spine.push((**arg).clone());
            head = func;
        }
        scrut_spine.reverse();
        if scrut_spine.len() < num_params + num_indices {
            return false;
        }
        let scrut_indices = &scrut_spine[num_params..num_params + num_indices];

        let Some(ctor_indices) = self.ctor_return_index_args(ctor_name, scrutinee_ty) else {
            return false;
        };
        if ctor_indices.len() != num_indices {
            return false;
        }

        // Impossible iff some index position witnesses a contradiction, by either
        // of two sound criteria:
        //   (a) constructor-head clash — both sides reduce to *distinct
        //       constructors of the same inductive*, which can never be equal even
        //       with free variables in their arguments (`succ n` vs `zero`); OR
        //   (b) two *ground* (closed) values that are not definitionally equal.
        // Criterion (a) subsumes the variable-index GADT case (`Vec α (succ n)`
        // omitting `nil`); (b) keeps the original closed-value behavior.
        scrut_indices
            .iter()
            .zip(ctor_indices.iter())
            .any(|(scrut_idx, ctor_idx)| {
                self.index_heads_clash(scrut_idx, ctor_idx)
                    || (Self::is_ground_index(scrut_idx)
                        && Self::is_ground_index(ctor_idx)
                        && !self.is_def_eq(scrut_idx, ctor_idx))
            })
    }

    /// The single index value of an indexed-family scrutinee type, together with
    /// the index inductive's name — or `None` when the family is not single-index
    /// or the index head is not a registered constructor's inductive.
    ///
    /// For `Vec α (Nat.succ n)` this returns `(Nat.succ n, "Nat")`.
    fn single_index_value(&self, scrutinee_ty: &Expr, type_name: &str) -> Option<(Expr, Name)> {
        let ind = self.env.get_inductive(&Name::from_string(type_name))?;
        if ind.num_indices != 1 {
            return None;
        }
        let num_params = ind.num_params as usize;
        let scrutinee_w = self.whnf(
            &self
                .metas
                .instantiate_levels(&self.metas.instantiate(scrutinee_ty)),
        );
        let mut spine: Vec<Expr> = Vec::new();
        let mut head = &scrutinee_w;
        while let ExprKind::App(func, arg) = head.kind() {
            spine.push((**arg).clone());
            head = func;
        }
        spine.reverse();
        if spine.len() != num_params + 1 {
            return None;
        }
        let index_val = spine.into_iter().next_back()?;
        // The index value's head must be a constructor (the GADT-refinement
        // discipline: a *concrete* index lets us discriminate); recover its
        // inductive so we can use that inductive's `.rec` as the discriminator.
        let (_, index_ind) = self.index_head_ctor(&index_val)?;
        Some((index_val, index_ind))
    }

    /// Whether the match `arms` over scrutinee type `type_name` legitimately
    /// omits at least one constructor that is *index-impossible* (its return
    /// index can never unify with the scrutinee's). Used to decide whether an
    /// index-discriminating motive is needed for the omitted branch.
    ///
    /// A constructor is "covered" when some arm names it (a `Ctor`/`Var`-nullary
    /// pattern resolving to it) or the match has a catch-all (`Wildcard`/binder
    /// `Var`) arm — in which case nothing is omitted. Returns `true` only when an
    /// *uncovered* constructor is provably index-impossible.
    pub(in crate::infer) fn match_omits_index_impossible_ctor(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        type_name: &str,
        scrutinee_ty: &Expr,
    ) -> bool {
        let Some(ind_info) = self
            .env
            .get_inductive(&Name::from_string(type_name))
            .cloned()
        else {
            return false;
        };
        // A catch-all arm covers every constructor: nothing is omitted.
        let has_catch_all = arms.iter().any(|arm| match &arm.pattern {
            SurfacePattern::Wildcard => true,
            SurfacePattern::Var(name) => self.resolve_ctor_name(name, type_name).is_none(),
            _ => false,
        });
        if has_catch_all {
            return false;
        }
        let mut any_impossible = false;
        for ctor_name in &ind_info.constructor_names {
            let covered = arms.iter().any(|arm| {
                self.top_level_ctor_target_name(type_name, &arm.pattern)
                    .as_deref()
                    .map(Name::from_string)
                    .as_ref()
                    == Some(ctor_name)
            });
            if covered {
                continue;
            }
            if self.ctor_index_is_impossible(ctor_name, scrutinee_ty) {
                any_impossible = true;
            } else {
                // An uncovered *possible* constructor means the match is genuinely
                // non-exhaustive; do not engage the discriminating motive (let the
                // normal path reject it).
                return false;
            }
        }
        any_impossible
    }

    /// Build the body of an **index-discriminating motive** for a single-index
    /// GADT match that legitimately omits index-impossible constructors.
    ///
    /// The returned expression is the motive *body*, to be placed under the
    /// motive's `(index) (major)` lambda telescope — so `BVar(0)` is the major
    /// premise and `BVar(1)` is the index value. Its shape is:
    ///
    /// ```text
    /// @I.rec.{u+1, …} params… (fun (_ : I params…) => Sort u)
    ///   minor_c0 … minor_c{m-1}    -- one per constructor of the index inductive I
    ///   BVar(1)                    -- the index value
    /// ```
    ///
    /// where each `minor_cᵢ = fun (field₀ … fieldₖ) (ih₀ … ihⱼ) => Rᵢ`, with
    /// `Rᵢ = branch_ty` when `cᵢ` is the scrutinee's index-constructor head (the
    /// *reachable* branch) and `Rᵢ = PUnit.{u}` otherwise (every *impossible*
    /// branch). Reducing the motive at the scrutinee's actual index therefore
    /// yields `branch_ty`, while reducing it at an omitted impossible
    /// constructor's index yields `PUnit.{u}` — which `PUnit.unit.{u}` inhabits
    /// with no axiom and no `sorry`.
    ///
    /// SOUNDNESS: the construction is checked by the kernel (it re-checks the
    /// whole lowered `T.casesOn` application). `I.rec` is the genuine recursor of
    /// the index inductive, applied per the standard recursor argument layout
    /// (`params → motive → minors → … → major`), so the discriminator iota-reduces
    /// exactly as the kernel expects. `branch_ty` references only outer free
    /// variables (never the index/major BVars), so it is placed verbatim under the
    /// minor's field/IH binders.
    ///
    /// Returns `None` (callers fall back to the existing constant/dependent motive)
    /// when the index inductive has no registered `.rec`, is itself indexed
    /// (`num_indices > 0` — out of scope for this targeted single-level
    /// discriminator), or its recursor metadata does not decompose cleanly.
    pub(in crate::infer) fn build_index_discriminating_motive_body(
        &mut self,
        scrutinee_ty: &Expr,
        type_name: &str,
        branch_ty: &Expr,
    ) -> Result<Option<(Expr, Level)>, ElabError> {
        self.with_optional_temporary_local_scope(|this| {
            Ok(this.build_index_discriminating_motive_body_probe(
                scrutinee_ty,
                type_name,
                branch_ty,
            ))
        })
    }

    /// Side-effecting implementation of the optional discriminator probe. The
    /// public wrapper above rolls back the complete elaboration state whenever
    /// this returns `None`, so failed metadata/sort probes cannot contaminate the
    /// constant-motive fallback.
    fn build_index_discriminating_motive_body_probe(
        &mut self,
        scrutinee_ty: &Expr,
        type_name: &str,
        branch_ty: &Expr,
    ) -> Option<(Expr, Level)> {
        let (index_val, index_ind) = self.single_index_value(scrutinee_ty, type_name)?;
        let (scrut_index_ctor, _) = self.index_head_ctor(&index_val)?;

        let ind_info = self
            .authenticate_inductive_metadata(&index_ind)
            .ok()?
            .clone();
        // Keep the discriminator simple and sound: the index inductive itself must
        // be non-indexed, so its `.rec` minors are `(fields…) (ihs…) => result`
        // (no extra index binders to thread). Covers Nat, Bool, and enum tags.
        if ind_info.num_indices != 0 {
            return None;
        }
        let rec_name = Name::from_string(&format!("{index_ind}.rec"));
        let rec_val = self.env.get_recursor(&rec_name).cloned()?;
        self.authenticate_recursor_cached(&rec_name).ok()?;
        // Native single-motive recursor in the standard layout only.
        if rec_val.num_motives != 1
            || rec_val.arg_order != clean_kernel::RecursorArgOrder::MajorAfterMinors
            || rec_val.num_params != ind_info.num_params
            || rec_val.num_indices != ind_info.num_indices
            || rec_val.num_minors as usize != ind_info.constructor_names.len()
            || rec_val.rules.len() != ind_info.constructor_names.len()
            || ind_info.all_names.len() != 1
        {
            return None;
        }

        // The result-sort universe: `branch_ty : Sort u`, and `PUnit.{u} : Sort u`
        // matches, so the discriminating motive maps `I → Sort u`.
        let u = self.infer_sort(branch_ty).ok()?;

        // Recover the index inductive's own parameters from the index value's
        // spine (e.g. the `α` in a `Vec α`-indexed-by-`List α` family). These are
        // applied to `I.rec`, `I`'s constructors, and the motive domain.
        let index_val_w = self.whnf(
            &self
                .metas
                .instantiate_levels(&self.metas.instantiate(&index_val)),
        );
        let (ctor_info, _) = self
            .authenticate_constructor_metadata(&scrut_index_ctor)
            .ok()?;
        let ctor_info = ctor_info.clone();
        if ctor_info.inductive_name != index_ind
            || ctor_info.num_params != ind_info.num_params
            || ctor_info.level_params.len() != ind_info.level_params.len()
        {
            return None;
        }
        let index_levels = match index_val_w.get_app_fn().kind() {
            ExprKind::Const(name, levels)
                if name == &scrut_index_ctor && levels.len() == ctor_info.level_params.len() =>
            {
                levels.to_vec()
            }
            _ => return None,
        };
        let mut index_spine: Vec<Expr> = Vec::new();
        let mut index_head = &index_val_w;
        while let ExprKind::App(func, arg) = index_head.kind() {
            index_spine.push((**arg).clone());
            index_head = func;
        }
        index_spine.reverse();
        if index_spine.len() != (ctor_info.num_params as usize + ctor_info.num_fields as usize) {
            return None;
        }
        let index_params = index_spine[..ind_info.num_params as usize].to_vec();
        if index_params.len() != ind_info.num_params as usize {
            return None;
        }

        // `I params…` — the recursor's parameter prefix and the motive domain.
        let i_applied = {
            let mut e = Expr::const_(index_ind.clone(), index_levels.clone());
            for p in &index_params {
                e = Expr::app(e, p.clone());
            }
            e
        };

        // Discriminating motive for `I.rec`: `fun (_ : I params…) => Sort u`.
        let rec_motive = Expr::lam(
            BinderInfo::Default,
            i_applied.clone(),
            Expr::sort(u.clone()),
        );

        // Recursor levels: `[motive_universe, …I.level_params]`. The motive maps
        // into `Sort u`, so the motive universe is `succ u` (the sort `Sort u`
        // itself lives in `Sort (u+1)`). Prop-only index inductives (no motive
        // universe param) are excluded — they cannot host a `Sort u` motive for
        // `u > 0` anyway, and our `num_motives == 1`/`MajorAfterMinors` gate plus
        // this check keep us on the large-eliminating recursors (Nat, enums).
        let rec_levels: Vec<Level> = {
            let ind_count = ind_info.level_params.len();
            if rec_val.level_params.len() == ind_count + 1 {
                let mut v = Vec::with_capacity(rec_val.level_params.len());
                v.push(Level::succ(u.clone()));
                v.extend(index_levels.clone());
                v
            } else if rec_val.level_params.len() == ind_count {
                // Prop-only recursor: cannot carry a Sort-u motive. Bail.
                return None;
            } else {
                return None;
            }
        };

        // Authenticate the complete rule packet before assembling any minor.
        // A missing rule is not evidence that the constructor is non-recursive,
        // and recursive flags must describe every constructor field exactly.
        let mut index_minor_plan = Vec::with_capacity(ind_info.constructor_names.len());
        for (ctor_name, rule) in ind_info.constructor_names.iter().zip(&rec_val.rules) {
            let (ctor_info, authenticated_parent) =
                self.authenticate_constructor_metadata(ctor_name).ok()?;
            if &rule.constructor_name != ctor_name || ctor_info.inductive_name != index_ind {
                return None;
            }
            if authenticated_parent.name != index_ind {
                return None;
            }
            let num_fields = ctor_info.num_fields as usize;
            if rule.num_fields as usize != num_fields || rule.recursive_fields.len() != num_fields {
                return None;
            }
            index_minor_plan.push((
                ctor_name.clone(),
                num_fields,
                rule.recursive_fields.iter().filter(|&&b| b).count(),
            ));
        }

        // Build one minor per constructor of the index inductive.
        let (punit_u, _) = self.punit_dummy_at_result_sort(branch_ty).ok()??;
        let mut rec_app = {
            let mut e = Expr::const_(rec_name.clone(), rec_levels);
            for p in &index_params {
                e = Expr::app(e, p.clone());
            }
            e
        };
        rec_app = Expr::app(rec_app, rec_motive);

        for (ctor_name, num_fields, num_ihs) in &index_minor_plan {
            // The reachable head returns `branch_ty`; every other head `PUnit.{u}`.
            // `branch_ty` mentions only outer FVars, so it is binder-depth-stable
            // and placed verbatim under the field/IH binders.
            let result = if ctor_name == &scrut_index_ctor {
                branch_ty.clone()
            } else {
                punit_u.clone()
            };

            // `fun (field₀ … fieldₖ) (ih₀ … ihⱼ) => result`. The exact field/IH
            // binder *types* are irrelevant to the result (it ignores them), so we
            // use `I params…` placeholders for fields and `Sort u` for IHs — the
            // kernel only checks the minor's *type* (a Pi telescope ending in
            // `Sort u`), which is satisfied since `result : Sort u` for either
            // branch and the binder domains are well-formed sorts/types.
            let mut minor = result;
            for _ in 0..*num_ihs {
                minor = Expr::lam(BinderInfo::Default, Expr::sort(u.clone()), minor);
            }
            // Reuse the central exact-spine routine: it authenticates the
            // constructor/inductive/constant packet, instantiates precisely the
            // declared parameters and rejects partial or overapplied returns.
            let field_tys = self.compute_ctor_field_types(ctor_name, &i_applied).ok()?;
            if field_tys.len() != *num_fields {
                return None;
            }
            for j in (0..*num_fields).rev() {
                minor = Expr::lam(BinderInfo::Default, field_tys[j].clone(), minor);
            }
            rec_app = Expr::app(rec_app, minor);
        }

        // Major premise of `I.rec`: the index value (BVar(1) under the motive's
        // (index)(major) telescope).
        rec_app = Expr::app(rec_app, Expr::bvar(1));

        Some((rec_app, u))
    }

    /// Synthesize the minor premise for a GADT-impossible constructor that the
    /// user omitted from a refined match (constant-motive `casesOn` path).
    ///
    /// The branch is unreachable at runtime (its index can never match the
    /// scrutinee's), so under the constant motive `fun _ => branch_ty` the minor
    /// only has to be *some* well-typed term of `branch_ty`, abstracted over the
    /// constructor's fields. We use a genuine default value of `branch_ty` (a
    /// nullary constructor, via `try_default_value_of_type`) — keeping the result
    /// axiom-free and kernel-checkable. Returns `None` when no such inhabitant
    /// exists, so the caller falls back to the existing behavior rather than
    /// fabricating a value.
    fn synthesize_impossible_ctor_minor(
        &mut self,
        ctor_name: &Name,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Expr>, ElabError> {
        // When an index-discriminating motive is in force, the omitted impossible
        // branch's minor type is `PUnit.{u}` (the motive returns `PUnit` at this
        // constructor's index head), so `PUnit.unit.{u}` discharges it with no
        // axiom — even when `branch_ty` itself has no closed inhabitant (e.g. a
        // bare type variable `α`).
        if let Some(u) = self.match_index_discriminating_punit.clone() {
            let unit = Expr::const_(Name::from_string("PUnit.unit"), vec![u]);
            let body = wrap_with_extra_params(unit, extra_param_info);
            return self
                .wrap_ctor_fallback_alt(body, ctor_name, scrutinee_ty)
                .map(Some);
        }
        // Under a *dependent* (index-refining) motive the omitted branch's minor
        // type is the per-arm `motive idx(ctorᵢ)… (ctorᵢ fields…)`, NOT the
        // first-arm `branch_ty`. For an index-impossible constructor that
        // per-arm type is the constructor's *own* refined return type — which
        // the constructor (or a sibling) genuinely inhabits. Example: `Vec.dup :
        // Vec α (succ n) → Vec α (succ n)` omitting `nil` has nil's per-arm type
        // `Vec α Nat.zero`, inhabited by `Vec.nil`. Compute that per-arm type and
        // take its default value, keeping the term axiom-free.
        if self.match_dependent_motive.is_some() {
            let arm_ty =
                self.dependent_arm_branch_ty(branch_ty, &ctor_name.to_string(), scrutinee_ty, &[])?;
            if let Some(default) = self.try_default_value_of_type(&arm_ty)? {
                let body = wrap_with_extra_params(default, extra_param_info);
                return self
                    .wrap_ctor_fallback_alt(body, ctor_name, scrutinee_ty)
                    .map(Some);
            }
        }
        // Otherwise (constant motive): the minor only has to be *some* well-typed
        // term of `branch_ty`, so use a genuine default value if one exists.
        let Some(default) = self.try_default_value_of_type(branch_ty)? else {
            return Ok(None);
        };
        let body = wrap_with_extra_params(default, extra_param_info);
        self.wrap_ctor_fallback_alt(body, ctor_name, scrutinee_ty)
            .map(Some)
    }

    pub(in crate::infer) fn wrap_ctor_fallback_alt(
        &self,
        alt: Expr,
        ctor_name: &Name,
        scrutinee_ty: &Expr,
    ) -> Result<Expr, ElabError> {
        let ctor_info = self.env.get_constructor(ctor_name).ok_or_else(|| {
            ElabError::InternalInvariant(format!(
                "missing registered constructor metadata `{ctor_name}` while building a fallback minor"
            ))
        })?;
        if ctor_info.num_fields == 0 {
            // Even a nullary constructor must cross the authenticated metadata
            // boundary: this catches a registry/constant disagreement instead
            // of letting the branch bypass field extraction entirely.
            self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
            return Ok(alt);
        }

        let field_tys = self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
        if field_tys.len() != ctor_info.num_fields as usize {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` declares {} fields but exposes {} field types",
                ctor_info.num_fields,
                field_tys.len()
            )));
        }
        let mut wrapped = alt;
        for field_ty in field_tys.into_iter().rev() {
            wrapped = Expr::lam(BinderInfo::Default, field_ty, wrapped);
        }
        Ok(wrapped)
    }

    fn rewrite_top_level_match_ctor_dispatch_arm(
        &mut self,
        arm: &clean_parser::SurfaceMatchArm,
        scrutinee_ty: &Expr,
    ) -> Result<clean_parser::SurfaceMatchArm, ElabError> {
        match &arm.pattern {
            SurfacePattern::As(name, inner_pat) => {
                let (pattern, alias_value) =
                    self.rewrite_as_pattern_inner("match arm pattern", scrutinee_ty, inner_pat)?;
                Ok(clean_parser::SurfaceMatchArm {
                    span: arm.span,
                    pattern,
                    body: wrap_alias_surface_body(name, alias_value, &arm.body),
                })
            }
            _ => Ok(arm.clone()),
        }
    }

    pub(in crate::infer) fn top_level_ctor_target_name(
        &self,
        type_name: &str,
        pattern: &SurfacePattern,
    ) -> Option<String> {
        match pattern {
            SurfacePattern::Ctor(ctor_name, _) => {
                Some(self.ctor_pattern_full_name(ctor_name, type_name))
            }
            SurfacePattern::Lit(SurfaceLit::Nat(0)) => Some(format!("{type_name}.zero")),
            SurfacePattern::Lit(SurfaceLit::Nat(_)) | SurfacePattern::NumeralAdd(_, _) => {
                Some(format!("{type_name}.succ"))
            }
            SurfacePattern::Var(name) => {
                self.resolve_ctor_name(name, type_name).filter(|full_ctor| {
                    self.env
                        .get_constructor(&Name::from_string(full_ctor))
                        .is_some_and(|info| info.num_fields == 0)
                })
            }
            SurfacePattern::As(_, inner) => self.top_level_ctor_target_name(type_name, inner),
            _ => None,
        }
    }

    /// Field sub-patterns of a *concrete* top-level dispatch arm, aligned to the
    /// target constructor's full field list, for the column-split lowering.
    ///
    /// * `Ctor(name, subs)` → `subs`, with nested `n + k` numeral-adds
    ///   normalized to constructor form and expanded to the constructor's
    ///   explicit field count (`..` ellipsis / implicit fields filled with
    ///   wildcards). Returns `None` if the pattern names a different constructor.
    /// * `Lit(Nat(k))` / `NumeralAdd(inner, k)` → the single `Nat.succ` field
    ///   sub-pattern (the predecessor), only when `ctor_name` is `Nat.succ`.
    ///
    /// Returns `None` for any shape outside this envelope so the caller defers to
    /// the legacy chain.
    fn ctor_dispatch_arm_field_pats(
        &mut self,
        ctor_name: &Name,
        pattern: &SurfacePattern,
        type_name: &str,
    ) -> Result<Option<Vec<SurfacePattern>>, ElabError> {
        let ctor_name_str = ctor_name.to_string();
        match pattern {
            SurfacePattern::Ctor(pat_ctor, subs) => {
                let full_ctor = self.ctor_pattern_full_name(pat_ctor, type_name);
                if full_ctor != ctor_name_str {
                    return Ok(None);
                }
                let normalized: Vec<SurfacePattern> = subs
                    .iter()
                    .map(normalize_nested_nat_numeral_add_pattern)
                    .collect();
                self.expand_implicit_ctor_field_patterns(
                    "match arm pattern",
                    &full_ctor,
                    &normalized,
                )
                .map(Some)
            }
            SurfacePattern::Lit(SurfaceLit::Nat(k)) if *k > 0 => {
                if ctor_name_str != format!("{type_name}.succ") {
                    return Ok(None);
                }
                Ok(match desugar_nonzero_nat_lit(*k) {
                    SurfacePattern::Ctor(_, subs) => Some(subs),
                    _ => None,
                })
            }
            SurfacePattern::NumeralAdd(inner, k) if *k > 0 => {
                if ctor_name_str != format!("{type_name}.succ") {
                    return Ok(None);
                }
                Ok(match desugar_nat_numeral_add_pattern(inner, *k) {
                    SurfacePattern::Ctor(_, subs) => Some(subs),
                    _ => None,
                })
            }
            _ => Ok(None),
        }
    }

    pub(in crate::infer) fn build_ctor_value(
        &self,
        ctor_name: &Name,
        scrutinee_ty: &Expr,
        field_fvars: &[FVarId],
    ) -> Result<Expr, ElabError> {
        let ctor_info = self.env.get_constructor(ctor_name).ok_or_else(|| {
            ElabError::InternalInvariant(format!(
                "missing registered constructor metadata `{ctor_name}` while rebuilding a constructor value"
            ))
        })?;
        let field_tys = self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
        if field_fvars.len() != field_tys.len() {
            return Err(ElabError::InternalInvariant(format!(
                "constructor value `{ctor_name}` received {} field variables for {} authenticated fields",
                field_fvars.len(),
                field_tys.len()
            )));
        }

        let scrutinee_ty = self.metas.instantiate(scrutinee_ty);
        let scrutinee_ty = self.metas.instantiate_levels(&scrutinee_ty);
        let scrutinee_ty = self.whnf(&scrutinee_ty);
        let levels = match scrutinee_ty.get_app_fn().kind() {
            ExprKind::Const(_, levels) if levels.len() == ctor_info.level_params.len() => {
                levels.to_vec()
            }
            _ => {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor value `{ctor_name}` cannot recover its {} universe levels from scrutinee `{scrutinee_ty:?}`",
                    ctor_info.level_params.len()
                )));
            }
        };

        let mut value = Expr::const_(ctor_name.clone(), levels);
        let params = self.extract_type_args(&scrutinee_ty, ctor_info.num_params);
        if params.len() != ctor_info.num_params as usize {
            return Err(ElabError::InternalInvariant(format!(
                "constructor value `{ctor_name}` cannot recover its {} parameters from scrutinee `{scrutinee_ty:?}`",
                ctor_info.num_params
            )));
        }
        for param in params {
            value = Expr::app(value, param);
        }
        for fvar in field_fvars {
            value = Expr::app(value, Expr::fvar(*fvar));
        }
        Ok(value)
    }

    #[allow(clippy::too_many_arguments)]
    fn compile_ctor_catch_all_alt(
        &mut self,
        ctor_name: &Name,
        arm: &clean_parser::SurfaceMatchArm,
        arm_idx: usize,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Expr>, ElabError> {
        match &arm.pattern {
            SurfacePattern::Wildcard => {
                if self.match_dependent_motive.is_some() {
                    // Under a DEPENDENT motive (e.g. the equation-wrapped
                    // `match h :` motive, audit d01) this expanded minor's
                    // expected type is the motive at THIS constructor's
                    // pattern instance, so the fields must be real locals
                    // (the blind `wrap_ctor_fallback_alt` lambdas cannot
                    // express `motive (ctor fields…)`).
                    let field_tys = self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
                    let mut field_fvars: Vec<(FVarId, Expr)> = Vec::with_capacity(field_tys.len());
                    for (idx, field_ty) in field_tys.iter().enumerate() {
                        let prior_fvars: Vec<FVarId> =
                            field_fvars.iter().map(|(f, _)| *f).collect();
                        let field_ty = Self::open_field_type_with_fvars(field_ty, &prior_fvars);
                        let fvar =
                            self.push_local(format!("_match_ctor_field_{idx}"), field_ty.clone());
                        field_fvars.push((fvar, field_ty));
                    }
                    let field_ids = field_fvars
                        .iter()
                        .map(|(fvar, _)| *fvar)
                        .collect::<Vec<_>>();
                    let ctor_value = self.build_ctor_value(ctor_name, scrutinee_ty, &field_ids)?;
                    let arm_ty = self.arm_branch_ty(branch_ty, &ctor_value);
                    let arm_body =
                        self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
                    if arm_idx > 0 {
                        self.check_arm_type(&arm_body, &arm_ty, arm_idx)?;
                    }
                    let mut result = wrap_with_extra_params(arm_body, extra_param_info);
                    for (fvar, field_ty) in field_fvars.iter().rev() {
                        self.pop_local();
                        result = result.abstract_fvar(*fvar);
                        result = Expr::lam(BinderInfo::Default, field_ty.clone(), result);
                    }
                    return Ok(Some(result));
                }
                let arm_body =
                    self.elaborate_with_expected_type(&arm.body, Some(branch_ty.clone()))?;
                if arm_idx > 0 {
                    self.check_arm_type(&arm_body, branch_ty, arm_idx)?;
                }
                let arm_body = wrap_with_extra_params(arm_body, extra_param_info);
                self.wrap_ctor_fallback_alt(arm_body, ctor_name, scrutinee_ty)
                    .map(Some)
            }
            SurfacePattern::Var(name) => {
                let field_tys = self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
                let mut field_fvars: Vec<(FVarId, Expr)> = Vec::with_capacity(field_tys.len());
                for (idx, field_ty) in field_tys.iter().enumerate() {
                    // Open dependent field types against the preceding fields so a
                    // later field's type references its sibling by `FVar` (see
                    // `open_field_type_with_fvars`).
                    let prior_fvars: Vec<FVarId> = field_fvars.iter().map(|(f, _)| *f).collect();
                    let field_ty = Self::open_field_type_with_fvars(field_ty, &prior_fvars);
                    let fvar =
                        self.push_local(format!("_match_ctor_field_{idx}"), field_ty.clone());
                    field_fvars.push((fvar, field_ty));
                }

                let field_ids = field_fvars
                    .iter()
                    .map(|(fvar, _)| *fvar)
                    .collect::<Vec<_>>();
                let ctor_value = self.build_ctor_value(ctor_name, scrutinee_ty, &field_ids)?;
                // Per-ctor expected type under a dependent motive (constant
                // motives get `branch_ty` back unchanged).
                let arm_ty = self.arm_branch_ty(branch_ty, &ctor_value);
                let alias_fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                let arm_body =
                    self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
                if arm_idx > 0 {
                    self.check_arm_type(&arm_body, &arm_ty, arm_idx)?;
                }
                let arm_body = wrap_with_extra_params(arm_body, extra_param_info);
                self.pop_local();
                let mut result = Expr::let_named(
                    Name::from_string(name),
                    scrutinee_ty.clone(),
                    ctor_value,
                    arm_body.abstract_fvar(alias_fvar),
                    false,
                );

                for (fvar, field_ty) in field_fvars.iter().rev() {
                    self.pop_local();
                    result = result.abstract_fvar(*fvar);
                    result = Expr::lam(BinderInfo::Default, field_ty.clone(), result);
                }

                Ok(Some(result))
            }
            _ => Ok(None),
        }
    }

    /// Compile the minor premise for `ctor_name` by *column-splitting* its
    /// fields, when several relevant arms share this top-level constructor but
    /// differ in their field sub-patterns (Bug #15 multi-column `match a, b`,
    /// Bug #40 iterated `Nat.succ` peeling with no wildcard).
    ///
    /// The prior fallback-chaining path compiled the terminal arm of such a
    /// chain standalone, rejecting its non-matching inner constructors even
    /// when a *sibling* arm covers them. This instead
    /// binds `ctor_name`'s fields to fresh named locals and re-lowers the field
    /// sub-patterns as a genuine nested `match` over those fields, reusing the
    /// proven single-scrutinee match compiler column-by-column. Each column ends
    /// up dispatched by a real `casesOn` with a minor for every constructor:
    /// exhaustive shapes produce a sorry-free term the kernel accepts; a
    /// non-exhaustive column falls through to an explicit elaboration error.
    ///
    /// Returns `Ok(None)` (defer to the legacy chain) whenever the arm shapes
    /// fall outside the conservative envelope handled here, so working single-
    /// arm / wildcard-catch-all shapes keep their existing lowering byte-for-byte.
    fn compile_ctor_field_column_split(
        &mut self,
        ctor_name: &Name,
        rows: &[(Vec<SurfacePattern>, SurfaceExpr)],
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Expr>, ElabError> {
        // This is a speculative rescue lane: its error is deliberately ignored
        // by the caller in favor of the legacy compiler. Make the entire attempt
        // transactional so a failed nested elaboration cannot leave committed
        // metas, pending levels, cache entries, or partially-restored locals.
        self.with_optional_temporary_local_scope(|this| {
            this.compile_ctor_field_column_split_inner(
                ctor_name,
                rows,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
            )
        })
    }

    fn compile_ctor_field_column_split_inner(
        &mut self,
        ctor_name: &Name,
        rows: &[(Vec<SurfacePattern>, SurfaceExpr)],
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Expr>, ElabError> {
        let Some(ctor_info) = self.env.get_constructor(ctor_name).cloned() else {
            return Ok(None);
        };
        let num_fields = ctor_info.num_fields as usize;
        if num_fields == 0 || rows.is_empty() {
            return Ok(None);
        }
        // Every relevant arm must supply exactly one explicit sub-pattern per
        // field. We only handle that shape here; anything else defers.
        if rows.iter().any(|(pats, _)| pats.len() != num_fields) {
            return Ok(None);
        }

        // Bind the constructor's fields as fresh *named* locals so the synthetic
        // surface match can reference them by `Ident`. Field types are opened
        // against the preceding fields (dependent-field discipline, mirroring
        // `elaborate_ctor_arm`). The `next_fvar` counter salts the names so
        // nested column splits never collide.
        let salt = self.next_fvar;
        let field_tys = self.compute_ctor_field_types(ctor_name, scrutinee_ty)?;
        if field_tys.len() != num_fields {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` declares {num_fields} fields but exposes {} field types",
                field_tys.len()
            )));
        }
        let mut field_bindings: Vec<(FVarId, Expr, String)> = Vec::with_capacity(num_fields);
        for (idx, field_ty) in field_tys.into_iter().enumerate() {
            let prior_fvars: Vec<FVarId> = field_bindings.iter().map(|(f, _, _)| *f).collect();
            let field_ty = Self::open_field_type_with_fvars(&field_ty, &prior_fvars);
            let name = format!("__csplit_{salt}_{idx}");
            let fvar = self.push_local(name.clone(), field_ty.clone());
            field_bindings.push((fvar, field_ty, name));
        }

        let field_names: Vec<String> = field_bindings.iter().map(|(_, _, n)| n.clone()).collect();
        let column_tys: Vec<Expr> = field_bindings.iter().map(|(_, ty, _)| ty.clone()).collect();

        // Build the nested surface match tree over the field columns and
        // elaborate it against `branch_ty` with the field locals in scope. Pop
        // the field locals on every exit path.
        let lowered = (|| -> Result<Option<Expr>, ElabError> {
            let rows_vec: Vec<(Vec<SurfacePattern>, Vec<(String, String)>, SurfaceExpr)> = rows
                .iter()
                .map(|(pats, body)| (pats.clone(), Vec::new(), body.clone()))
                .collect();
            let Some(surface) =
                self.build_column_split_surface(&field_names, &column_tys, &rows_vec)?
            else {
                return Ok(None);
            };
            let saved_expected = self.current_expected_type.clone();
            self.set_expected_type(Some(branch_ty.clone()));
            let body = self.elaborate_with_expected_type(&surface, Some(branch_ty.clone()));
            self.set_expected_type(saved_expected);
            let body = body?;
            // `elaborate_with_expected_type` drives inference but does not by
            // itself prove that a synthesized nested match consumed its entire
            // eliminator telescope. A partial `Nat.casesOn`, for example, has a
            // function result and used to escape this speculative lane as if it
            // had `branch_ty`. Authenticate the completed column before it is
            // abstracted into the outer constructor minor.
            let actual_ty = self.infer_type(&body)?;
            if !self.is_def_eq(&actual_ty, branch_ty) {
                return Err(ElabError::TypeMismatch {
                    expected: format!("complete column-split branch of type {branch_ty:?}"),
                    actual: format!("{actual_ty:?}"),
                });
            }
            Ok(Some(body))
        })();

        // Abstract the field locals back into the minor premise's field lambdas.
        let mut result = match lowered {
            Ok(Some(body)) => wrap_with_extra_params(body, extra_param_info),
            other => {
                for _ in &field_bindings {
                    self.pop_local();
                }
                return other;
            }
        };
        for (fvar, field_ty, _) in field_bindings.iter().rev() {
            self.pop_local();
            result = result.abstract_fvar(*fvar);
            result = Expr::lam(BinderInfo::Default, field_ty.clone(), result);
        }
        Ok(Some(result))
    }

    /// Recursively build a nested single-scrutinee surface `match` that splits
    /// `rows` column-by-column over `field_names` (with parallel column types
    /// `column_tys`). Used by [`Self::compile_ctor_field_column_split`]; the
    /// produced surface tree is elaborated + kernel-checked by the caller.
    ///
    /// Each row carries the remaining column patterns, a list of *pending `let`
    /// bindings* `(user_var, column_ident)` — a column consumed by a binder
    /// sub-pattern binds the user's variable to that column's fresh field local
    /// so the body still sees it — and the body.
    ///
    /// * Base case (`field_names` empty): the first (earliest source) row wins;
    ///   its body is wrapped in its pending `let` bindings.
    /// * Otherwise split on the first field. Rows are grouped, in first-seen
    ///   order, by the head of their first sub-pattern (constructors — including
    ///   `Nat` literals, `n + k` numeral-adds normalized to `Nat.succ`/
    ///   `Nat.zero`, and a bare `Var` that resolves to a constructor of the
    ///   *column's* type, e.g. `true`/`false` on a `Bool` column). Each
    ///   constructor group re-binds that constructor's fields with fresh names
    ///   and recurses with those field columns (and their types) prepended to the
    ///   remaining columns. A genuine binder (`Var` naming no constructor, or
    ///   `_`) is a catch-all that joins every constructor group AND forms a
    ///   trailing default arm; a named binder records a pending `let`.
    ///
    /// Returns `None` for any first sub-pattern shape outside this envelope
    /// (as-patterns, or-patterns, inaccessible, q-patterns, …), so the caller
    /// defers to the legacy path rather than misbuild.
    fn build_column_split_surface(
        &mut self,
        field_names: &[String],
        column_tys: &[Expr],
        rows: &[(Vec<SurfacePattern>, Vec<(String, String)>, SurfaceExpr)],
    ) -> Result<Option<SurfaceExpr>, ElabError> {
        use clean_parser::{Span, SurfaceMatchArm};

        let Some((col, rest_fields)) = field_names.split_first() else {
            // No columns left: the first (earliest source) row wins; wrap its
            // body in the pending `let` bindings (outermost binding first).
            let Some((_, binds, body)) = rows.first() else {
                return Ok(None);
            };
            let mut result = body.clone();
            for (name, value_ident) in binds.iter().rev() {
                result = SurfaceExpr::let_expr(
                    name.clone(),
                    SurfaceExpr::ident(value_ident.clone()),
                    result,
                );
            }
            return Ok(Some(result));
        };
        let Some((col_ty, rest_tys)) = column_tys.split_first() else {
            return Ok(None);
        };
        let col_type_name = self.get_type_name(col_ty).ok();
        if rows.is_empty() {
            return Ok(None);
        }

        // Single-column classification of a row's first sub-pattern, resolving a
        // bare `Var` against the column's type so a nullary-constructor alias
        // (`true`, `Option.none`, …) dispatches as a constructor, not a binder.
        // A `Var` that names no constructor is a genuine binder — `Binder(name)`.
        enum Head {
            Ctor(String, Vec<SurfacePattern>),
            Binder(Option<String>),
        }
        let classify = |this: &mut Self, pat: &SurfacePattern| -> Option<Head> {
            match pat {
                SurfacePattern::Wildcard => Some(Head::Binder(None)),
                SurfacePattern::Var(name) => {
                    match col_type_name
                        .as_deref()
                        .and_then(|tn| this.resolve_ctor_name(name, tn))
                    {
                        Some(full_ctor) => Some(Head::Ctor(full_ctor, vec![])),
                        None => Some(Head::Binder(Some(name.clone()))),
                    }
                }
                SurfacePattern::Ctor(name, subs) => {
                    // Resolve the (possibly short) constructor name against the
                    // column type, exactly as the `Var` branch above does — a
                    // nested arm writes `some (some n)` with the short `some`,
                    // and downstream metadata lookups (`compute_ctor_field_types`
                    // on `group.ctor`) require the fully-qualified `Option.some`.
                    let full = col_type_name
                        .as_deref()
                        .and_then(|tn| this.resolve_ctor_name(name, tn))
                        .unwrap_or_else(|| name.clone());
                    Some(Head::Ctor(full, subs.clone()))
                }
                SurfacePattern::Lit(SurfaceLit::Nat(0)) => {
                    Some(Head::Ctor("Nat.zero".to_string(), vec![]))
                }
                SurfacePattern::Lit(SurfaceLit::Nat(k)) => match desugar_nonzero_nat_lit(*k) {
                    SurfacePattern::Ctor(name, subs) => Some(Head::Ctor(name, subs)),
                    _ => None,
                },
                SurfacePattern::NumeralAdd(inner, k) => {
                    match desugar_nat_numeral_add_pattern(inner, *k) {
                        SurfacePattern::Ctor(name, subs) => Some(Head::Ctor(name, subs)),
                        // `n + 0` degenerates to a bare binder.
                        SurfacePattern::Var(n) => Some(Head::Binder(Some(n.clone()))),
                        SurfacePattern::Wildcard => Some(Head::Binder(None)),
                        _ => None,
                    }
                }
                _ => None,
            }
        };

        // A row after its first column has been consumed. `binds` carries any new
        // pending `let` from a binder column (a named binder binds `col`).
        type SplitRow = (Vec<SurfacePattern>, Vec<(String, String)>, SurfaceExpr);

        // Classify every row's first sub-pattern ONCE, preserving source order.
        //
        // B05 (docs/plans/GAP_SWEEP_2026-07-09.md, SILENT_WRONG_SUSPECT-14):
        // row priority is POSITIONAL. A binder ("catch-all") row spliced into a
        // constructor group must keep its place *relative to* that group's
        // concrete rows — the previous implementation collected binder rows
        // separately and APPENDED them after the concrete rows, so under
        // cross-column ("diagonal") overlap (`match a, b with | 0, _ => 1
        // | _, 0 => 2 | _, _ => 3`) the inner column saw row 2's concrete `0`
        // BEFORE row 1's spliced wildcard, and the base case's "first row
        // wins" kernel-certified `f 0 0 = 2` where Lean computes 1. Lean
        // processes match alternatives strictly top-down: `State.alts` in
        // lean4 `src/Lean/Meta/Match/Match.lean` stays in source order through
        // every specialization step (`processConstructor` / `processValue` /
        // `processVariable` filter-preserve the alternative list), i.e.
        // Maranget's S(c, P) specialization — the first matching row wins and
        // later overlapping rows only cover the residual.
        let mut classified: Vec<(Head, SplitRow)> = Vec::with_capacity(rows.len());
        for (pats, binds, body) in rows {
            let Some((first, rest_pats)) = pats.split_first() else {
                return Ok(None);
            };
            let Some(head) = classify(self, first) else {
                return Ok(None);
            };
            classified.push((head, (rest_pats.to_vec(), binds.clone(), body.clone())));
        }

        // Constructor groups in first-seen order (short-name keyed, one
        // consistent arity per group; a mismatch defers to the legacy path).
        // Group ORDER is irrelevant to semantics — the emitted arms carry
        // mutually-exclusive constructor patterns — only row order within each
        // group's specialized matrix matters.
        struct Group {
            ctor: String,
            arity: usize,
        }
        let mut groups: Vec<Group> = Vec::new();
        for (head, _) in &classified {
            if let Head::Ctor(name, subs) = head {
                let short = name.rsplit('.').next().unwrap_or(name);
                match groups
                    .iter()
                    .find(|g| g.ctor.rsplit('.').next().unwrap_or(&g.ctor) == short)
                {
                    Some(g) if g.arity == subs.len() => {}
                    Some(_) => return Ok(None),
                    None => groups.push(Group {
                        ctor: name.clone(),
                        arity: subs.len(),
                    }),
                }
            }
        }

        // Extend a binder row's pending `let`s with this column's binding (a
        // named binder binds `col`; a wildcard binds nothing).
        let binder_row_binds = |name: &Option<String>, binds: &[(String, String)]| {
            let mut binds = binds.to_vec();
            if let Some(name) = name {
                binds.push((name.clone(), col.clone()));
            }
            binds
        };

        // Default-arm rows: the rows whose first sub-pattern is a genuine
        // binder, in source order (Maranget's default matrix D(P)).
        let catch_all_rows: Vec<SplitRow> = classified
            .iter()
            .filter_map(|(head, (rest_pats, binds, body))| match head {
                Head::Binder(name) => Some((
                    rest_pats.clone(),
                    binder_row_binds(name, binds),
                    body.clone(),
                )),
                Head::Ctor(_, _) => None,
            })
            .collect();

        let mut arms: Vec<SurfaceMatchArm> = Vec::with_capacity(groups.len() + 1);
        for group in &groups {
            let group_short = group.ctor.rsplit('.').next().unwrap_or(&group.ctor);
            let sub_names: Vec<String> = (0..group.arity).map(|j| format!("{col}__f{j}")).collect();
            let arm_pattern = SurfacePattern::Ctor(
                group.ctor.clone(),
                sub_names
                    .iter()
                    .map(|n| SurfacePattern::Var(n.clone()))
                    .collect(),
            );
            // Specialize the matrix for this constructor IN SOURCE ORDER
            // (B05, see above): a row naming this constructor contributes its
            // field sub-patterns; a binder row also matches it and contributes
            // all-wildcard fields (plus its pending `let`); a row naming a
            // DIFFERENT constructor is irrelevant to this group and is
            // dropped. Relative row order is preserved throughout, so the
            // recursion's "first row wins" base case is Lean's first-row
            // priority.
            let next_rows: Vec<SplitRow> = classified
                .iter()
                .filter_map(|(head, (rest_pats, binds, body))| match head {
                    Head::Ctor(name, subs)
                        if name.rsplit('.').next().unwrap_or(name) == group_short =>
                    {
                        let mut row_pats = subs.clone();
                        row_pats.extend_from_slice(rest_pats);
                        Some((row_pats, binds.clone(), body.clone()))
                    }
                    Head::Ctor(_, _) => None,
                    Head::Binder(name) => {
                        let mut row_pats = vec![SurfacePattern::Wildcard; group.arity];
                        row_pats.extend_from_slice(rest_pats);
                        Some((row_pats, binder_row_binds(name, binds), body.clone()))
                    }
                })
                .collect();
            // The constructor's field types become the new leading column types.
            let group_ctor_ty =
                self.compute_ctor_field_types(&Name::from_string(&group.ctor), col_ty)?;
            if group_ctor_ty.len() != group.arity {
                return Ok(None);
            }
            let mut next_fields = sub_names;
            next_fields.extend_from_slice(rest_fields);
            let mut next_tys = group_ctor_ty;
            next_tys.extend_from_slice(rest_tys);
            let Some(inner) =
                self.build_column_split_surface(&next_fields, &next_tys, &next_rows)?
            else {
                return Ok(None);
            };
            arms.push(SurfaceMatchArm {
                span: Span::dummy(),
                pattern: arm_pattern,
                body: inner,
            });
        }

        // A trailing catch-all arm (from binder-first rows) so the column is
        // total even for constructors no arm named concretely. Only emitted when
        // a catch-all row exists — an exhaustive concrete-constructor cover needs
        // no default, and omitting it keeps the match fail-closed for genuinely
        // missing constructors. ALL catch-all rows (not just the first) recurse
        // into the default: when a column carries only binders (e.g. the head of
        // a `cons` pattern), the remaining columns must still discriminate every
        // row, so the whole catch-all matrix is threaded forward in source order.
        // Each row's binder for `col` was already recorded as a pending `let`.
        if !catch_all_rows.is_empty() {
            let Some(inner) =
                self.build_column_split_surface(rest_fields, rest_tys, &catch_all_rows)?
            else {
                return Ok(None);
            };
            arms.push(SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Wildcard,
                body: inner,
            });
        }

        if arms.is_empty() {
            return Ok(None);
        }

        Ok(Some(SurfaceExpr::Match(
            Span::dummy(),
            None,
            Box::new(SurfaceExpr::ident(col.clone())),
            arms,
        )))
    }

    #[allow(clippy::too_many_arguments)]
    fn compile_ctor_dispatch_alt_chain(
        &mut self,
        ctor_name: &Name,
        arms: &[clean_parser::SurfaceMatchArm],
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Expr>, ElabError> {
        let ctor_name_str = ctor_name.to_string();
        let mut relevant = Vec::new();

        for (arm_idx, arm) in arms.iter().enumerate() {
            let normalized = self.rewrite_top_level_match_ctor_dispatch_arm(arm, scrutinee_ty)?;
            match &normalized.pattern {
                SurfacePattern::Wildcard => {
                    relevant.push((arm_idx, normalized, true));
                    break;
                }
                SurfacePattern::Var(name) => {
                    let resolved = self.resolve_ctor_name(name, type_name);
                    let nullary_ctor = resolved.filter(|full_ctor| {
                        self.env
                            .get_constructor(&Name::from_string(full_ctor))
                            .is_some_and(|info| info.num_fields == 0)
                    });
                    if let Some(full_ctor) = nullary_ctor {
                        if full_ctor == ctor_name_str {
                            relevant.push((arm_idx, normalized, false));
                            break;
                        }
                    } else {
                        relevant.push((arm_idx, normalized, true));
                        break;
                    }
                }
                _ => {
                    let Some(full_ctor) =
                        self.top_level_ctor_target_name(type_name, &normalized.pattern)
                    else {
                        return Ok(None);
                    };
                    if full_ctor == ctor_name_str {
                        relevant.push((arm_idx, normalized, false));
                    }
                }
            }
        }

        if relevant.is_empty() {
            // No user arm names this constructor. In a GADT-style refined match
            // (scrutinee `T concreteIdx`), the user legitimately omits the
            // constructors whose own return index can never unify with the
            // scrutinee's concrete index. The eliminator still requires a minor
            // for every constructor, so synthesize one for an *index-impossible*
            // constructor (an unreachable, dead-code branch). When the
            // constructor is NOT provably impossible — a genuinely reachable but
            // un-handled case — return `None` to preserve the existing
            // (non-exhaustive) behavior rather than fabricating a branch.
            if self.ctor_index_is_impossible(ctor_name, scrutinee_ty) {
                if let Some(minor) = self.synthesize_impossible_ctor_minor(
                    ctor_name,
                    scrutinee_ty,
                    branch_ty,
                    extra_param_info,
                )? {
                    return Ok(Some(minor));
                }
            }
            return Ok(None);
        }

        // Column-split path (Bug #15 multi-column, Bug #40 deep `Nat.succ`).
        // When several concrete arms share this top-level constructor but differ
        // in their *field* sub-patterns, the fallback-chaining loop below compiles
        // the terminal arm standalone and rejects its non-matching inner
        // constructors — even when a sibling arm covers them.
        // Detect that shape and re-lower the shared constructor's fields as a
        // genuine nested `match` over the field columns, reusing the proven
        // single-scrutinee compiler (exhaustive → sorry-free; non-exhaustive →
        // explicit failure). We try this *before* the chain so an exhaustive
        // concrete cover is compiled as one total field match.
        //
        // Gated to the case the chain gets wrong: an all-concrete-constructor
        // cover (no wildcard catch-all — that path already has a real body) with
        // at least one field sub-pattern that itself selects a constructor.
        // Tactic `Hole` bodies are valid here too: the refine bridge preserves
        // common captured-field identities across the resulting leaf goals, so
        // each hole remains attached to the binders surrounding the match term.
        let has_catch_all = relevant.iter().any(|(_, _, c)| *c);
        let relevant_patterns: Vec<SurfacePattern> = relevant
            .iter()
            .map(|(_, arm, _)| arm.pattern.clone())
            .collect();
        let relevant_bodies: Vec<SurfaceExpr> = relevant
            .iter()
            .map(|(_, arm, _)| arm.body.clone())
            .collect();
        if !has_catch_all {
            let mut split_rows = Some(Vec::with_capacity(relevant_patterns.len()));
            for (pat, body) in relevant_patterns.iter().zip(relevant_bodies.iter()) {
                let Some(sub_pats) =
                    self.ctor_dispatch_arm_field_pats(ctor_name, pat, type_name)?
                else {
                    split_rows = None;
                    break;
                };
                split_rows
                    .as_mut()
                    .expect("split rows remain present until the first unsupported pattern")
                    .push((sub_pats, body.clone()));
            }
            if let Some(rows) = split_rows {
                // Only worth splitting when some field column actually dispatches
                // on a constructor (a `Ctor`/`Nat` literal/`n + k`, or a `Var`
                // that resolves to a constructor of that field's type — e.g.
                // `true`/`false` on a `Bool` field). Otherwise the legacy chain is
                // already correct and byte-for-byte cheaper.
                let field_type_names: Vec<Option<String>> = self
                    .compute_ctor_field_types(ctor_name, scrutinee_ty)?
                    .iter()
                    .map(|ft| self.get_type_name(ft).ok())
                    .collect();
                let has_dispatch_field = rows.iter().any(|(sub_pats, _)| {
                    sub_pats.iter().enumerate().any(|(idx, p)| match p {
                        SurfacePattern::Ctor(_, _)
                        | SurfacePattern::Lit(_)
                        | SurfacePattern::NumeralAdd(_, _) => true,
                        SurfacePattern::Var(name) => field_type_names
                            .get(idx)
                            .and_then(|tn| tn.as_deref())
                            .and_then(|tn| self.resolve_ctor_name(name, tn))
                            .is_some(),
                        _ => false,
                    })
                });
                if has_dispatch_field {
                    // Swallow a split-elaboration error: the legacy chain below is
                    // still a valid (kernel-checked) result, so a failed rescue
                    // must never turn a working decl into a hard error. The split
                    // helper is a full local/meta/level transaction, so fallback
                    // begins from the exact entry state.
                    if let Ok(Some(split)) = self.compile_ctor_field_column_split(
                        ctor_name,
                        &rows,
                        scrutinee_ty,
                        branch_ty,
                        extra_param_info,
                    ) {
                        if !split.has_sorry() {
                            return Ok(Some(split));
                        }
                    }
                }
            }
        }

        let mut compiled = None;
        for (arm_idx, arm, catch_all) in relevant.into_iter().rev() {
            let alt = if catch_all {
                let Some(alt) = self.compile_ctor_catch_all_alt(
                    ctor_name,
                    &arm,
                    arm_idx,
                    scrutinee_ty,
                    branch_ty,
                    extra_param_info,
                )?
                else {
                    return Ok(None);
                };
                alt
            } else {
                match &arm.pattern {
                    SurfacePattern::Ctor(ctor_name, sub_pats) => self.elaborate_ctor_arm(
                        ctor_name,
                        sub_pats,
                        &arm,
                        arm_idx,
                        type_name,
                        scrutinee_ty,
                        branch_ty,
                        extra_param_info,
                        false,
                        compiled.as_ref(),
                    )?,
                    SurfacePattern::Lit(SurfaceLit::Nat(0)) => self.elaborate_lit_arm(
                        type_name,
                        &SurfaceLit::Nat(0),
                        &arm,
                        arm_idx,
                        scrutinee_ty,
                        branch_ty,
                        extra_param_info,
                    )?,
                    SurfacePattern::Lit(SurfaceLit::Nat(k)) => {
                        let desugared = desugar_nonzero_nat_lit(*k);
                        let SurfacePattern::Ctor(ctor_name, sub_pats) = desugared else {
                            unreachable!("desugar_nonzero_nat_lit returns Ctor for k > 0")
                        };
                        self.elaborate_ctor_arm(
                            &ctor_name,
                            &sub_pats,
                            &arm,
                            arm_idx,
                            type_name,
                            scrutinee_ty,
                            branch_ty,
                            extra_param_info,
                            false,
                            compiled.as_ref(),
                        )?
                    }
                    SurfacePattern::NumeralAdd(inner_pat, k) if *k <= 1 => self
                        .elaborate_numeral_add_arm(
                            type_name,
                            inner_pat,
                            *k,
                            &arm,
                            arm_idx,
                            scrutinee_ty,
                            branch_ty,
                            extra_param_info,
                        )?,
                    SurfacePattern::NumeralAdd(inner_pat, k) => {
                        let desugared = desugar_nat_numeral_add_pattern(inner_pat.as_ref(), *k);
                        let SurfacePattern::Ctor(ctor_name, sub_pats) = desugared else {
                            unreachable!("desugar_nat_numeral_add_pattern returns Ctor for k > 1")
                        };
                        self.elaborate_ctor_arm(
                            &ctor_name,
                            &sub_pats,
                            &arm,
                            arm_idx,
                            type_name,
                            scrutinee_ty,
                            branch_ty,
                            extra_param_info,
                            false,
                            compiled.as_ref(),
                        )?
                    }
                    SurfacePattern::Var(name) => self.elaborate_var_arm(
                        name,
                        &arm,
                        arm_idx,
                        type_name,
                        scrutinee_ty,
                        branch_ty,
                        extra_param_info,
                    )?,
                    _ => return Ok(None),
                }
            };
            compiled = Some(alt);
        }

        Ok(compiled)
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn try_build_ctor_ordered_match_alts(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Vec<Expr>>, ElabError> {
        self.with_optional_temporary_local_scope(|this| {
            this.try_build_ctor_ordered_match_alts_inner(
                arms,
                type_name,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
            )
        })
    }

    fn try_build_ctor_ordered_match_alts_inner(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Vec<Expr>>, ElabError> {
        let ind_name = Name::from_string(type_name);
        let Some(ind_info) = self.env.get_inductive(&ind_name).cloned() else {
            return Ok(None);
        };

        let mut ordered = Vec::with_capacity(ind_info.constructor_names.len());
        for ctor_name in &ind_info.constructor_names {
            let Some(alt) = self.compile_ctor_dispatch_alt_chain(
                ctor_name,
                arms,
                type_name,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
            )?
            else {
                return Ok(None);
            };
            ordered.push(alt);
        }

        Ok(Some(ordered))
    }

    /// `use_rec` analogue of [`Self::try_build_ctor_ordered_match_alts`].
    ///
    /// Builds the `T.rec` minor premises in constructor *declaration* order
    /// (the order the recursor expects), expanding a trailing wildcard/`_` arm
    /// across every otherwise-unhandled constructor. Unlike the `casesOn`
    /// builder this also emits the induction-hypothesis binders a recursor minor
    /// premise carries for each recursive field.
    ///
    /// Returns `None` (so the caller falls back to the legacy source-order
    /// loop) for any arm shape outside the conservative envelope handled here:
    /// concrete constructor patterns with plain variable/wildcard field
    /// patterns, and at most one catch-all wildcard. This is exactly the shape
    /// of TrustIr `Ty.bitWidth` (Track R), whose source arms are neither in
    /// declaration order nor exhaustive without the trailing `_ => none`.
    /// Build the primary type's `T.rec` minor premises for a *nested* inductive
    /// by reading each minor's exact expected type off the kernel-built recursor.
    ///
    /// For a nested inductive (`Ty` with `Tuple : List Ty -> Ty`, inducing the
    /// auxiliary `Ty._List`) the recursor `Ty.rec` is a *mutual* recursor: its
    /// telescope is
    ///   `Π params, Π motiveᵀʸ, Π motive_List, Π minor₁ … minor_n, Π major, …`
    /// where each `minorᵢ` has type `Π fields&IHs, motive (ctorᵢ fields…)`. The
    /// IH for the `Tuple` field is typed by `motive_List`, NOT by `branch_ty` —
    /// exactly the premise the hand-reconstructed builder mis-typed.
    ///
    /// Here we instead build the recursor head applied to params + every motive
    /// (the primary motive `fun _ : Ty => branch_ty` and one constant aux motive
    /// `fun _ : Ty._List => branch_ty` per auxiliary type), `infer_type` it, and
    /// peel the first `num_minors` Π binders. Each peeled minor type is the
    /// authoritative expected type: we push fresh fvars for its binders, fill the
    /// conclusion with the matching arm's body (concrete arm or catch-all for a
    /// primary constructor; a default `branch_ty` value for an auxiliary-type
    /// constructor, whose minor is dead code under a primary-typed scrutinee),
    /// and abstract the binders back into lambdas of those precise domain types.
    ///
    /// SOUNDNESS: every binder type comes verbatim from the kernel recursor's own
    /// signature, and the assembled application is re-checked by the kernel. We
    /// never fabricate a field/IH type; the conclusion is always the real motive
    /// applied to the real constructor, which `whnf` reduces to `branch_ty` for
    /// the constant motives we supply. Returns `Ok(None)` (defer to legacy) for
    /// any shape we cannot build precisely (non-trivial conclusion, missing
    /// recursor, non-simple arm patterns), never a mis-typed minor.
    pub(in crate::infer) fn try_build_nested_rec_alts_from_telescope(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        ind_info: &clean_kernel::InductiveVal,
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Vec<Expr>>, ElabError> {
        // Only simple constructor / catch-all arm patterns (mirrors the gate in
        // `try_build_ctor_ordered_rec_alts`); anything fancier defers to legacy.
        for arm in arms {
            match &arm.pattern {
                SurfacePattern::Wildcard => {}
                SurfacePattern::Var(_) => {}
                SurfacePattern::Ctor(_, sub_pats) => {
                    if sub_pats
                        .iter()
                        .any(|p| !matches!(p, SurfacePattern::Var(_) | SurfacePattern::Wildcard))
                    {
                        return Ok(None);
                    }
                }
                _ => return Ok(None),
            }
        }

        let rec_name = Name::from_string(&format!("{type_name}.rec"));
        let Some(rec_val) = self.env.get_recursor(&rec_name).cloned() else {
            return Ok(None);
        };
        let num_minors = rec_val.num_minors as usize;
        let num_motives = rec_val.num_motives as usize;

        // The kernel records the complete minor order.  After nested restore the
        // erased auxiliary members are absent from `all_names`; their rule
        // slices live on `T.rec_1`, `T.rec_2`, ... and are re-keyed to the real
        // container constructors.  Use that metadata rather than recreating
        // pre-restore `T._List` names.
        let minor_rules = self.recursor_minor_rules(ind_info, &rec_val)?;
        let minor_plan: Vec<(Name, Vec<bool>)> = minor_rules
            .iter()
            .map(|rule| (rule.constructor_name.clone(), rule.recursive_fields.clone()))
            .collect();

        // Recursor universe levels, matching the caller's eliminator construction.
        let elim_levels = self.eliminator_levels(&rec_name, scrutinee_ty, branch_ty)?;

        // Build `T.rec params… motives…` — the head whose inferred type carries
        // the minor telescope. Every member sees the block's global motive
        // order, so a later ordinary mutual member's primary motive belongs in
        // its actual slot rather than slot zero.
        let mut head = self.apply_eliminator_params_count(
            Expr::const_(rec_name.clone(), elim_levels),
            scrutinee_ty,
            rec_val.num_params,
        )?;

        // Primary motive: `fun (_ : <scrutinee_ty>) => branch_ty`.
        let primary_motive =
            Expr::lam(BinderInfo::Default, scrutinee_ty.clone(), branch_ty.clone());
        let selected_motive_idx =
            self.selected_motive_index(ind_info, num_motives, "ordered recursive mutual match")?;
        for motive_idx in 0..num_motives {
            if motive_idx == selected_motive_idx {
                head = Expr::app(head, primary_motive.clone());
            } else {
                // Read each restored/ordinary sibling motive domain directly
                // from the partially-applied recursor. In particular, a nested
                // helper motive is `(List Ty -> Sort _)`, not an erased name.
                let head_ty = self.infer_type(&head)?;
                let head_ty = self.whnf(&head_ty);
                let ExprKind::Pi(_, expected_motive, _) = head_ty.kind() else {
                    return Ok(None);
                };
                let aux_motive = self.constant_over_telescope(expected_motive, branch_ty.clone());
                head = Expr::app(head, aux_motive);
            }
        }

        // Inferred type of the head = `Π minor₁ … minor_n, Π major, concl`.
        let mut tele = self.infer_type(&head)?;
        let mut ordered: Vec<Expr> = Vec::with_capacity(num_minors);
        for (ctor_name, recursive_fields) in &minor_plan {
            let ExprKind::Pi(_, minor_dom, minor_cod) = self.whnf(&tele).kind().clone() else {
                // Telescope shorter than expected — bail rather than misbuild.
                return Ok(None);
            };
            let minor_ty = minor_dom.as_ref().clone();

            // Build the minor body for `ctor_name` against its exact expected type
            // `minor_ty`. Advance the telescope past this minor.
            let Some(alt) = self.build_minor_from_expected_type(
                ctor_name,
                &minor_ty,
                recursive_fields,
                arms,
                type_name,
                ind_info,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
            )?
            else {
                return Ok(None);
            };
            // Type-check the minor against its expected type before committing
            // (defensive: kernel re-checks the whole application anyway).
            ordered.push(alt);

            // Advance: the minor binder is non-dependent for a constant motive,
            // so instantiating with any well-typed placeholder of `minor_ty`
            // leaves the rest of the telescope unchanged. We instantiate the Pi
            // with a fresh fvar of the minor's type to step past it.
            let placeholder = self.push_local("_minor".to_string(), minor_ty.clone());
            tele = minor_cod.instantiate(&Expr::fvar(placeholder));
            self.pop_local();
        }

        Ok(Some(ordered))
    }

    /// Build one `T.rec` minor premise of the exact expected type `expected`
    /// (its full `Π fields&IHs, conclusion` shape), for constructor `ctor_name`.
    ///
    /// Pushes a fresh fvar for every Π binder of `expected` — the first
    /// `num_fields` are the constructor's fields, the rest are induction
    /// hypotheses (one per recursive field, in field order; this is the recursor
    /// minor layout, #643). For a concrete `.Ctor(vars…)` arm we name the field
    /// binders by the pattern variables and wire each recursive field's IH into
    /// `recursive_def_ctx.ih_map` so a self-call in the body (`elemTy.bitWidth`)
    /// is rewritten to that IH — exactly as `elaborate_rec_arm` does, but binding
    /// the fields/IHs at the recursor's EXACT domain types (so a nested field is
    /// bound at `Ty._List`, not the surface `List Ty`). The body is checked
    /// against the whnf-reduced conclusion, then the binders are abstracted back
    /// into lambdas of those precise domain types.
    ///
    /// An auxiliary-type constructor (dead code under a primary scrutinee) or a
    /// primary constructor covered only by a catch-all fills the conclusion with
    /// the catch-all body / a default value. Returns `Ok(None)` when neither an
    /// arm nor a default can fill the conclusion.
    #[allow(clippy::too_many_arguments)]
    fn build_minor_from_expected_type(
        &mut self,
        ctor_name: &Name,
        expected: &Expr,
        recursive_fields: &[bool],
        arms: &[clean_parser::SurfaceMatchArm],
        type_name: &str,
        ind_info: &clean_kernel::InductiveVal,
        _scrutinee_ty: &Expr,
        _branch_ty: &Expr,
        _extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Expr>, ElabError> {
        let is_primary = ind_info.constructor_names.iter().any(|c| c == ctor_name);

        // Track AA: for an AUXILIARY constructor (`Tree._List.nil` / `.cons`) of
        // a fused nested-mutual fold, the real minor body comes from the sibling
        // function's arms (`Tree.sizeList`'s `[] => 0` / `t :: rest => …`), NOT
        // from a default fill. Resolve the matching aux arm by short ctor name:
        // `nil` ↔ a `List.nil`/`[]` pattern, `cons` ↔ a `List.cons`/`_ :: _`
        // pattern. The arm is cloned so no `self`/field borrow is held across the
        // mutable binder loop below. This only fires when the auxiliary-arm
        // source is installed (a fused nested-mutual block) and the constructor
        // belongs to the matching container mirror, so ordinary single-function
        // recursion (where this is `None`) keeps the default-fill path verbatim.
        let aux_arm: Option<clean_parser::SurfaceMatchArm> = if is_primary {
            None
        } else {
            self.resolve_nested_mutual_aux_arm(ctor_name)
        };

        // Resolve which arm (if any) covers this constructor, and the trailing
        // catch-all arm (a bare wildcard, or a variable that is NOT a nullary-ctor
        // alias). Both are resolved up front so no `self` borrow is held across the
        // mutable binder loop below.
        let concrete_arm = self.find_concrete_arm_for_ctor(ctor_name, arms, type_name);
        let catch_all_arm: Option<&clean_parser::SurfaceMatchArm> =
            arms.iter().find(|arm| match &arm.pattern {
                SurfacePattern::Wildcard => true,
                SurfacePattern::Var(n) => self.resolve_ctor_name_const(n, type_name).is_none(),
                _ => false,
            });

        let num_fields = recursive_fields.len();
        // Pattern variable names for the chosen-arm's fields (if any). For a
        // primary ctor this is the matching `concrete_arm`; for an auxiliary
        // ctor it is the resolved `aux_arm` (whose `List.cons t rest` sub-pattern
        // names the field binders `t`/`rest`, so the IH for each recursive field
        // is keyed by those names and a sibling self-call `Tree.size t` /
        // `Tree.sizeList rest` rewrites to it).
        let pattern_source = aux_arm.as_ref().or(concrete_arm);
        let field_var_names: Option<Vec<String>> =
            pattern_source.and_then(|arm| match &arm.pattern {
                SurfacePattern::Ctor(_, sub_pats) => Some(
                    (0..num_fields)
                        .map(|i| match sub_pats.get(i) {
                            Some(SurfacePattern::Var(n)) => n.clone(),
                            _ => format!("_field_{i}"),
                        })
                        .collect(),
                ),
                // A nullary-ctor alias (bare `Var` naming the ctor) has no fields.
                _ => None,
            });

        // Peel the minor's Π telescope into fresh fvar binders, opening each
        // dependent domain against the binders already pushed. The first
        // `num_fields` binders are fields; the remainder are IHs in field order.
        let mut binders: Vec<(FVarId, Expr)> = Vec::new();
        let mut ih_map: HashMap<String, FVarId> = HashMap::new();
        let mut first_ih_fvar: Option<FVarId> = None;
        let recursive_field_positions: Vec<usize> = recursive_fields
            .iter()
            .enumerate()
            .filter(|(_, &r)| r)
            .map(|(i, _)| i)
            .collect();
        let expected_binder_count = num_fields + recursive_field_positions.len();

        let mut cursor = expected.clone();
        for binder_idx in 0..expected_binder_count {
            let whnf = self.whnf(&cursor);
            let ExprKind::Pi(_, dom, cod) = whnf.kind() else {
                for _ in &binders {
                    self.pop_local();
                }
                return Err(ElabError::TypeMismatch {
                    expected: format!(
                        "{expected_binder_count} constructor-field/IH binders for nested recursive minor `{ctor_name}`"
                    ),
                    actual: format!("minor telescope ended after {binder_idx} binders at {whnf:?}"),
                });
            };
            let dom = dom.as_ref().clone();
            let name = if binder_idx < num_fields {
                field_var_names
                    .as_ref()
                    .and_then(|ns| ns.get(binder_idx).cloned())
                    .unwrap_or_else(|| format!("_field_{binder_idx}"))
            } else {
                // IH binder: the (binder_idx - num_fields)-th recursive field.
                let ih_pos = binder_idx - num_fields;
                let field_pos = recursive_field_positions.get(ih_pos).copied();
                let fname = field_pos
                    .and_then(|fp| field_var_names.as_ref().and_then(|ns| ns.get(fp).cloned()))
                    .unwrap_or_else(|| format!("_ih_{ih_pos}"));
                format!("ih_{fname}")
            };
            let fvar = self.push_local(name.clone(), dom.clone());

            if binder_idx >= num_fields {
                // Register this IH for self-call rewriting, keyed by the field's
                // pattern-variable name (matches `elaborate_rec_arm`'s ih_map).
                let ih_pos = binder_idx - num_fields;
                if let Some(field_pos) = recursive_field_positions.get(ih_pos).copied() {
                    if let Some(fname) = field_var_names
                        .as_ref()
                        .and_then(|ns| ns.get(field_pos).cloned())
                    {
                        if fname != "_" && !fname.starts_with("_field_") {
                            ih_map.insert(fname, fvar);
                        }
                    }
                }
                if first_ih_fvar.is_none() {
                    first_ih_fvar = Some(fvar);
                }
            }

            binders.push((fvar, dom));
            cursor = cod.instantiate(&Expr::fvar(fvar));
        }
        // Stop at the authoritative field+IH prefix. The conclusion may itself
        // be Pi-valued when the match returns a function; those binders belong
        // to the branch result and must not be misclassified as extra IHs.
        let conclusion = self.whnf(&cursor);

        // Pick the body source: concrete arm, else catch-all (primary), else a
        // default value (auxiliary dead-code minor).
        let chosen_arm: Option<&clean_parser::SurfaceMatchArm> = if is_primary {
            concrete_arm.or(catch_all_arm)
        } else if let Some(ref a) = aux_arm {
            // Track AA: a fused nested-mutual fold supplies the REAL auxiliary
            // minor body (e.g. `Tree.size t + Tree.sizeList rest`) from the
            // sibling function's matching arm. This is the genuine fold — not a
            // degenerate `Nat.zero` default.
            Some(a)
        } else {
            // Auxiliary ctor minor with no aux-arm source: prefer a trailing
            // catch-all body, else default (dead code under a primary scrutinee).
            catch_all_arm
        };

        let body_opt: Option<Expr> = if let Some(arm) = chosen_arm {
            // Install IH context so self-calls in the body route to the IHs we
            // just bound, then elaborate the body against the exact conclusion.
            let saved_ctx = self.recursive_def_ctx.clone();
            if let Some(ref mut ctx) = self.recursive_def_ctx {
                if first_ih_fvar.is_some() {
                    ctx.ih_fvar = first_ih_fvar;
                    ctx.ih_type = Some(conclusion.clone());
                    ctx.ih_map = ih_map.clone();
                }
            }
            let res = self.elaborate_with_expected_type(&arm.body, Some(conclusion.clone()));
            self.recursive_def_ctx = saved_ctx;
            Some(res?)
        } else if is_primary {
            // A default inhabitant is valid only for an unreachable auxiliary
            // member. Filling an uncovered constructor of the selected type
            // would silently change a non-exhaustive recursive match into a
            // total function (and is especially easy to miss when the result is
            // PUnit). Refuse before the auxiliary/default path.
            for _ in &binders {
                self.pop_local();
            }
            return Err(ElabError::NotImplemented(format!(
                "non-exhaustive nested recursive match on `{type_name}`: missing primary constructor `{ctor_name}`"
            )));
        } else {
            self.try_default_value_of_type(&conclusion)?
        };

        let Some(mut body) = body_opt else {
            for _ in &binders {
                self.pop_local();
            }
            return Ok(None);
        };

        // Abstract the binders back into lambdas of their exact domain types.
        for (fvar, dom) in binders.iter().rev() {
            self.pop_local();
            body = body.abstract_fvar(*fvar);
            body = Expr::lam(BinderInfo::Default, dom.clone(), body);
        }
        Ok(Some(body))
    }

    /// Track AA: resolve the sibling-function arm that fills the auxiliary
    /// constructor `aux_ctor` of a fused nested-mutual fold.
    ///
    /// When `self.nested_mutual_aux_arms` is installed (a `{ T.f : T -> R,
    /// T.g : C T -> R }` block being fused into one `T.rec`), `T.g`'s arms
    /// supply the auxiliary minors of the `T._C` mirror. The mirror's ctors are
    /// `T._C.nil` / `T._C.cons` (matching the container `C`'s `C.nil` / `C.cons`
    /// by short name), so we match `T.g`'s arm whose pattern's constructor has
    /// the same SHORT name as `aux_ctor`'s last segment. A `[]` literal pattern
    /// parses as `List.nil`, `t :: rest` as `List.cons t rest` — both already
    /// carry the right short names. Returns a clone (no borrow held across the
    /// caller's mutable binder loop). `None` when no aux-arm source is installed,
    /// the constructor is not from the matching mirror, or no arm matches.
    fn resolve_nested_mutual_aux_arm(
        &self,
        aux_ctor: &Name,
    ) -> Option<clean_parser::SurfaceMatchArm> {
        let aux = self.nested_mutual_aux_arms.as_ref()?;
        // The aux ctor must belong to the fold's container. Pre-B0-B5 that was a
        // `<Parent>._<Container>` mirror (penultimate segment `_List`); post-B0-B5
        // (ed84e7d64) the aux is erased and re-keyed to the REAL container, so the
        // aux ctors are `List.nil`/`List.cons` (penultimate segment `List`). Accept
        // either form so the sibling arm still resolves for the fused fold.
        let ctor_str = aux_ctor.to_string();
        let mut segs = ctor_str.rsplit('.');
        let ctor_short = segs.next()?.to_string();
        let mirror_seg = segs.next()?; // pre-restore `_List`, restored `List`
        if mirror_seg != format!("_{}", aux.container_short) && mirror_seg != aux.container_short {
            return None;
        }
        // Find the sibling arm whose pattern's constructor short name matches.
        aux.arms
            .iter()
            .find(|arm| match &arm.pattern {
                SurfacePattern::Ctor(pat_ctor, _) => pat_ctor
                    .rsplit('.')
                    .next()
                    .map(|s| s.eq_ignore_ascii_case(&ctor_short))
                    .unwrap_or(false),
                _ => false,
            })
            .cloned()
    }

    /// Find a concrete arm (`.Ctor …` or a bare-identifier nullary-ctor alias)
    /// that handles `ctor_name`. Mirrors the resolution in
    /// `try_build_ctor_ordered_rec_alts`. Does not return catch-all arms.
    fn find_concrete_arm_for_ctor<'b>(
        &mut self,
        ctor_name: &Name,
        arms: &'b [clean_parser::SurfaceMatchArm],
        type_name: &str,
    ) -> Option<&'b clean_parser::SurfaceMatchArm> {
        let ctor_short = ctor_name
            .to_string()
            .rsplit('.')
            .next()
            .unwrap_or_default()
            .to_string();
        for arm in arms {
            match &arm.pattern {
                SurfacePattern::Ctor(pat_ctor, _) => {
                    let target = self.ctor_pattern_full_name(pat_ctor, type_name);
                    if target == ctor_name.to_string()
                        || target.rsplit('.').next() == Some(ctor_short.as_str())
                    {
                        return Some(arm);
                    }
                }
                SurfacePattern::Var(name)
                    if self
                        .resolve_ctor_name(name, type_name)
                        .map(|c| c == ctor_name.to_string())
                        .unwrap_or(false) =>
                {
                    return Some(arm);
                }
                _ => {}
            }
        }
        None
    }

    /// Non-`&mut self` constructor-name resolution for use inside closures.
    fn resolve_ctor_name_const(&self, name: &str, type_name: &str) -> Option<String> {
        // `resolve_ctor_name` takes `&mut self`; replicate its read-only effect
        // by checking the env for a constructor with this short name in scope.
        let candidate = format!("{type_name}.{name}");
        if self
            .env
            .get_constructor(&Name::from_string(&candidate))
            .is_some()
        {
            return Some(candidate);
        }
        if self.env.get_constructor(&Name::from_string(name)).is_some() {
            return Some(name.to_string());
        }
        None
    }

    pub(in crate::infer) fn try_build_ctor_ordered_rec_alts(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Vec<Expr>>, ElabError> {
        self.with_optional_temporary_local_scope(|this| {
            this.try_build_ctor_ordered_rec_alts_inner(
                arms,
                type_name,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
            )
        })
    }

    fn try_build_ctor_ordered_rec_alts_inner(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Vec<Expr>>, ElabError> {
        let ind_name = Name::from_string(type_name);
        let Some(ind_info) = self.env.get_inductive(&ind_name).cloned() else {
            return Ok(None);
        };

        // Nested / mutual inductives (`all_names.len() > 1`, e.g. a `Ty` whose
        // `Tuple : List Ty -> Ty` constructor induces an auxiliary `Ty._List`)
        // use a *mutual* recursor whose minor premises carry induction
        // hypotheses typed by the *auxiliary* motive, not by `branch_ty`, and
        // whose nested-constructor minor for `Tuple` has the shape
        // `(t : Ty._List) → motive_List t → motive (Ty.Tuple t)` — a shape the
        // hand-reconstructed `recursive_fields`/`branch_ty` minor builder gets
        // wrong (it confuses the `Ty.Tuple` minor with the `Ty._List.cons`
        // minor, mis-typing the premise). The telescope-driven builder below
        // reads each minor premise's EXACT expected type off the kernel-built
        // recursor and binds lambdas of those precise domain types, so the
        // nested case is handled soundly (TrustIr `Ty.bitWidth`, Track W). It is
        // gated on the simple-motive case (`extra_param_info` empty): a
        // varying-parameter motive (#1386) folds extra Pis into every minor
        // conclusion, which the telescope walk does not yet account for, so that
        // shape still defers to the legacy loop.
        let rec_name = Name::from_string(&format!("{type_name}.rec"));
        let is_multi_motive = self
            .env
            .get_recursor(&rec_name)
            .is_some_and(|rec| rec.num_motives > 1);
        if is_multi_motive {
            if extra_param_info.is_empty() {
                return self.try_build_nested_rec_alts_from_telescope(
                    arms,
                    &ind_info,
                    type_name,
                    scrutinee_ty,
                    branch_ty,
                    extra_param_info,
                );
            }
            // A varying-parameter motive (#1386) folds extra Pis into every minor
            // conclusion; combined with nested IHs that is a distinct shape we do
            // not yet build precisely, so defer to the legacy loop.
            return Ok(None);
        }

        // Classify the arm shapes. The existing fast path requires every arm to
        // be a simple constructor pattern (variable/wildcard fields) or a
        // catch-all. A *nested* constructor sub-pattern (a ctor/lit head inside a
        // field, e.g. `.bool b :: rest` over `List Value`) used to bail straight
        // to the legacy source-order loop — which cannot merge the *several* arms
        // that map to one recursor constructor (`.bool … :: rest` and the
        // catch-all `_ :: rest` both target `List.cons`), losing the induction
        // hypothesis on the recursive tail. Detect the nested-head shape and, for
        // it, route through the dedicated per-constructor dispatch-chain builder
        // (Track G3) which installs the IH and folds the same-constructor arms
        // into one nested-`casesOn` minor. Anything else still defers.
        let mut has_nested_ctor_arms = false;
        for arm in arms {
            match &arm.pattern {
                SurfacePattern::Wildcard => {}
                SurfacePattern::Var(name) => {
                    let _ = self.resolve_ctor_name(name, type_name);
                }
                SurfacePattern::Ctor(_, sub_pats) => {
                    if sub_pats
                        .iter()
                        .any(|p| !matches!(p, SurfacePattern::Var(_) | SurfacePattern::Wildcard))
                    {
                        has_nested_ctor_arms = true;
                    }
                }
                _ => return Ok(None),
            }
        }

        if has_nested_ctor_arms {
            return self.try_build_nested_head_rec_alts(
                arms,
                &ind_info,
                type_name,
                scrutinee_ty,
                branch_ty,
                extra_param_info,
            );
        }

        let rec_name = Name::from_string(&format!("{type_name}.rec"));

        // Recursor rule metadata is authoritative for the IH telescope. Validate
        // every constructor before elaborating any arm: discovering a missing or
        // malformed later rule after earlier arms assigned metas would make an
        // `Ok(None)` fallback stateful. Never reinterpret missing metadata as
        // "this constructor is non-recursive".
        let Some(rec_info) = self.env.get_recursor(&rec_name).cloned() else {
            return Ok(None);
        };
        let mut ctor_recursive_fields = Vec::with_capacity(ind_info.constructor_names.len());
        for ctor_name in &ind_info.constructor_names {
            let Some(ctor_info) = self.env.get_constructor(ctor_name) else {
                return Ok(None);
            };
            let Some(rule) = rec_info
                .rules
                .iter()
                .find(|rule| &rule.constructor_name == ctor_name)
            else {
                return Ok(None);
            };
            let num_fields = ctor_info.num_fields as usize;
            if rule.num_fields as usize != num_fields || rule.recursive_fields.len() != num_fields {
                return Ok(None);
            }
            ctor_recursive_fields.push((ctor_name.clone(), rule.recursive_fields.clone()));
        }

        let mut ordered = Vec::with_capacity(ind_info.constructor_names.len());
        for (ctor_name, recursive_fields) in &ctor_recursive_fields {
            // Number of recursive fields = number of IH binders this minor
            // premise must carry, read from the prevalidated genuine rule.
            let ih_count = recursive_fields.iter().filter(|&&b| b).count();

            // Find the arm handling this constructor (concrete match wins over a
            // catch-all; the first concrete or first catch-all in source order).
            let ctor_short = ctor_name
                .to_string()
                .rsplit('.')
                .next()
                .unwrap_or_default()
                .to_string();
            let mut concrete: Option<(usize, &clean_parser::SurfaceMatchArm)> = None;
            let mut catch_all: Option<(usize, &clean_parser::SurfaceMatchArm)> = None;
            for (arm_idx, arm) in arms.iter().enumerate() {
                match &arm.pattern {
                    SurfacePattern::Ctor(pat_ctor, _) => {
                        let target = self.ctor_pattern_full_name(pat_ctor, type_name);
                        if target == ctor_name.to_string()
                            || target.rsplit('.').next() == Some(ctor_short.as_str())
                        {
                            if concrete.is_none() {
                                concrete = Some((arm_idx, arm));
                            }
                            break;
                        }
                    }
                    SurfacePattern::Var(name)
                        if self
                            .resolve_ctor_name(name, type_name)
                            .map(|c| c == ctor_name.to_string())
                            .unwrap_or(false) =>
                    {
                        if concrete.is_none() {
                            concrete = Some((arm_idx, arm));
                        }
                        break;
                    }
                    SurfacePattern::Wildcard | SurfacePattern::Var(_) if catch_all.is_none() => {
                        catch_all = Some((arm_idx, arm));
                        // Keep scanning: an explicit later arm could still name
                        // this constructor before the catch-all applies. (Lean
                        // forbids that, but be defensive.)
                    }
                    SurfacePattern::Wildcard | SurfacePattern::Var(_) => {}
                    _ => {}
                }
            }

            let alt = if let Some((arm_idx, arm)) = concrete {
                // Concrete constructor arm. `elaborate_rec_arm` builds the full
                // field + IH binder structure, routing the recursive call(s) in
                // the body through the induction hypotheses.
                match &arm.pattern {
                    SurfacePattern::Var(name) => {
                        // Nullary constructor named by a bare identifier alias:
                        // a plain value, no field/IH binders.
                        self.elaborate_var_arm(
                            name,
                            arm,
                            arm_idx,
                            type_name,
                            scrutinee_ty,
                            branch_ty,
                            extra_param_info,
                        )?
                    }
                    SurfacePattern::Ctor(pat_ctor, sub_pats) => {
                        let full_ctor = self.ctor_pattern_full_name(pat_ctor, type_name);
                        let normalized_sub_pats = self.expand_implicit_ctor_field_patterns(
                            "match arm pattern",
                            &full_ctor,
                            sub_pats,
                        )?;
                        if normalized_sub_pats.is_empty() {
                            // Nullary constructor: plain value, no field/IH binders.
                            let arm_ty = self.dependent_arm_branch_ty(
                                branch_ty,
                                &full_ctor,
                                scrutinee_ty,
                                &[],
                            )?;
                            let arm_body =
                                self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
                            wrap_with_extra_params(arm_body, extra_param_info)
                        } else {
                            self.elaborate_rec_arm(
                                &full_ctor,
                                &normalized_sub_pats,
                                &arm.body,
                                scrutinee_ty,
                                branch_ty,
                                arm_idx,
                                extra_param_info,
                            )?
                        }
                    }
                    _ => return Ok(None),
                }
            } else if let Some((arm_idx, arm)) = catch_all {
                // Catch-all for this constructor: build the body (a plain
                // `branch_ty` value) and wrap it with the constructor's field
                // lambdas followed by `ih_count` induction-hypothesis lambdas,
                // so the minor premise arity matches what `T.rec` expects.
                let Some(body) = self.compile_ctor_catch_all_alt(
                    ctor_name,
                    arm,
                    arm_idx,
                    scrutinee_ty,
                    branch_ty,
                    extra_param_info,
                )?
                else {
                    return Ok(None);
                };
                let mut alt = body;
                for _ in 0..ih_count {
                    let ih_ty = generalize_with_extra_params(branch_ty.clone(), extra_param_info);
                    alt = Expr::lam(BinderInfo::Default, ih_ty, alt);
                }
                alt
            } else {
                // No arm covers this constructor and there is no catch-all:
                // non-exhaustive. Defer to the legacy loop / error path.
                return Ok(None);
            };
            ordered.push(alt);
        }

        Ok(Some(ordered))
    }

    /// Track G3: build `T.rec` minors when at least one arm has a *nested
    /// constructor head* sub-pattern (a ctor/lit inside a field, e.g.
    /// `.bool b :: rest`). Several surface arms may map to the same recursor
    /// constructor (e.g. `.bool … :: rest` and the catch-all `_ :: rest` both
    /// target `List.cons`); this folds them into ONE minor per constructor that
    /// dispatches on the nested head via a `casesOn` chain, with each
    /// lower-priority arm's compiled minor serving as the fallback for the
    /// non-matching heads — and crucially installs the induction hypothesis for
    /// every recursive field, so a self-call on the recursive tail lowers to the
    /// IH rather than an unsolved placeholder.
    ///
    /// SOUNDNESS: each minor is assembled from the genuine `T.rec` recursor (the
    /// fields/IHs come from `elaborate_rec_arm_with_fallback`, which binds them in
    /// the recursor's minor-premise order) and the nested dispatch uses the real
    /// `Value.casesOn`; the whole application is re-checked by the kernel. Returns
    /// `Ok(None)` (defer to the legacy loop) for any shape outside this envelope
    /// rather than emit a mis-typed term.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::infer) fn try_build_nested_head_rec_alts(
        &mut self,
        arms: &[clean_parser::SurfaceMatchArm],
        ind_info: &clean_kernel::InductiveVal,
        type_name: &str,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
        extra_param_info: &[ExtraParamBinding],
    ) -> Result<Option<Vec<Expr>>, ElabError> {
        // Only the single-type (non nested-mutual) case. Post-B0-B5 a nested type
        // has `all_names.len() == 1` yet stays multi-motive, so also bail on the
        // `is_nested` flag — the telescope-driven builder handles it instead.
        if ind_info.all_names.len() > 1 || ind_info.is_nested {
            return Ok(None);
        }
        let rec_name = Name::from_string(&format!("{type_name}.rec"));
        let Some(rec_val) = self.env.get_recursor(&rec_name).cloned() else {
            return Ok(None);
        };

        // Validate every real recursor rule before any arm body is elaborated.
        // This probe may return `Ok(None)` to a legacy fallback, so discovering
        // malformed metadata after earlier alternatives mutated metas would be
        // stateful and missing rules must never mean "zero IHs".
        let mut ctor_recursive_fields = Vec::with_capacity(ind_info.constructor_names.len());
        for ctor_name in &ind_info.constructor_names {
            let Some(ctor_info) = self.env.get_constructor(ctor_name) else {
                return Ok(None);
            };
            let Some(rule) = rec_val
                .rules
                .iter()
                .find(|rule| &rule.constructor_name == ctor_name)
            else {
                return Ok(None);
            };
            let num_fields = ctor_info.num_fields as usize;
            if rule.num_fields as usize != num_fields || rule.recursive_fields.len() != num_fields {
                return Ok(None);
            }
            ctor_recursive_fields.push((ctor_name.clone(), rule.recursive_fields.clone()));
        }

        // Classify each arm's TOP-LEVEL pattern: which recursor constructor it
        // targets (a concrete `Ctor`/nullary alias) or whether it is a genuine
        // catch-all (covers every constructor). Anything else → defer.
        enum ArmTarget {
            Ctor(String),
            CatchAll,
        }
        let mut arm_targets: Vec<ArmTarget> = Vec::with_capacity(arms.len());
        for arm in arms {
            match &arm.pattern {
                SurfacePattern::Ctor(pat_ctor, _) => {
                    arm_targets.push(ArmTarget::Ctor(
                        self.ctor_pattern_full_name(pat_ctor, type_name),
                    ));
                }
                SurfacePattern::Wildcard => arm_targets.push(ArmTarget::CatchAll),
                SurfacePattern::Var(name) => match self.resolve_ctor_name(name, type_name) {
                    Some(full) => arm_targets.push(ArmTarget::Ctor(full)),
                    None => arm_targets.push(ArmTarget::CatchAll),
                },
                _ => return Ok(None),
            }
        }

        let mut ordered = Vec::with_capacity(ind_info.constructor_names.len());
        for (ctor_name, recursive_fields) in &ctor_recursive_fields {
            let ctor_str = ctor_name.to_string();
            let ctor_short = ctor_str.rsplit('.').next().unwrap_or_default();

            // Collect the arms covering this constructor, in source (priority)
            // order: every arm whose target is this ctor, plus catch-alls (which
            // cover it). Stop at the first catch-all — later arms are unreachable
            // for this constructor.
            let mut covering: Vec<(usize, &clean_parser::SurfaceMatchArm, bool)> = Vec::new();
            for (idx, (arm, target)) in arms.iter().zip(arm_targets.iter()).enumerate() {
                match target {
                    ArmTarget::Ctor(full) => {
                        let matches_ctor =
                            full == &ctor_str || full.rsplit('.').next() == Some(ctor_short);
                        if matches_ctor {
                            covering.push((idx, arm, false));
                        }
                    }
                    ArmTarget::CatchAll => {
                        covering.push((idx, arm, true));
                        break;
                    }
                }
            }

            if covering.is_empty() {
                // No arm and no catch-all covers this constructor.
                return Ok(None);
            }

            // Fold the covering arms into one minor, lowest-priority first so each
            // higher-priority arm's nested dispatch falls back to the already-built
            // minor for the same constructor.
            let mut compiled: Option<Expr> = None;
            for (arm_idx, arm, is_catch_all) in covering.into_iter().rev() {
                let alt = if is_catch_all {
                    // A genuine catch-all minor: build the body (which may itself
                    // recurse — it needs the IH too) wrapped in the constructor's
                    // field binders followed by `ih_count` IH binders, exactly as
                    // a `T.rec` minor premise expects. `elaborate_rec_arm` over a
                    // freshly synthesized all-wildcard sub-pattern installs the IHs
                    // and routes a self-call on the recursive field to them.
                    let wildcard_pats = vec![SurfacePattern::Wildcard; recursive_fields.len()];
                    self.elaborate_rec_arm(
                        &ctor_str,
                        &wildcard_pats,
                        &arm.body,
                        scrutinee_ty,
                        branch_ty,
                        arm_idx,
                        extra_param_info,
                    )?
                } else {
                    let SurfacePattern::Ctor(pat_ctor, sub_pats) = &arm.pattern else {
                        return Ok(None);
                    };
                    let full_ctor = self.ctor_pattern_full_name(pat_ctor, type_name);
                    let normalized_sub_pats = self.expand_implicit_ctor_field_patterns(
                        "match arm pattern",
                        &full_ctor,
                        sub_pats,
                    )?;
                    if normalized_sub_pats.is_empty() {
                        // Nullary constructor: plain value, no field/IH binders.
                        let arm_ty =
                            self.dependent_arm_branch_ty(branch_ty, &full_ctor, scrutinee_ty, &[])?;
                        let arm_body =
                            self.elaborate_with_expected_type(&arm.body, Some(arm_ty.clone()))?;
                        wrap_with_extra_params(arm_body, extra_param_info)
                    } else {
                        self.elaborate_rec_arm_with_fallback(
                            &full_ctor,
                            &normalized_sub_pats,
                            &arm.body,
                            scrutinee_ty,
                            branch_ty,
                            arm_idx,
                            extra_param_info,
                            compiled.as_ref(),
                        )?
                    }
                };
                compiled = Some(alt);
            }

            let Some(alt) = compiled else {
                return Ok(None);
            };
            ordered.push(alt);
        }

        Ok(Some(ordered))
    }
}

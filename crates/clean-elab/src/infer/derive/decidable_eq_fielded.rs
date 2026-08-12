// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real (sorry-free) `DecidableEq` for monomorphic, multi-constructor
//! inductives whose constructors carry NON-recursive fields, each with a
//! resolvable `DecidableEq` instance (e.g. `Color | rgb : Nat -> Color |
//! named : Nat -> Color`).
//!
//! Wave-1 only built a real decision procedure for all-nullary enums
//! (`decidable_eq_enum.rs`); fielded ctors fell back to `mk_sorry_with_level`
//! in `inductive.rs` — a LIVE `sorry` in a kernel-facing derive path. This
//! module discharges that obligation for the single-field-per-ctor (and
//! multi-field) non-recursive case by building the decision term from per-field
//! `DecidableEq` dispatch + `congrArg` + `noConfusion`, exactly like the
//! hand-written Nat/UInt `decEq`:
//!
//! ```text
//! fun (a b : X) =>
//!   X.casesOn (motive := fun a' => Decidable (a' = b)) a
//!     (fun fa.. => X.casesOn (motive := fun b' => Decidable (Cᵢ fa.. = b')) b
//!                    (fun fb.. => <same-ctor decision> | <isFalse noConfusion>)
//!                    ..)
//!     ..
//! ```
//!
//! Same-ctor decision (single field shown; multi-field nests):
//! ```text
//! Decidable.casesOn (decEq_T fa fb)
//!   (isFalse h => isFalse (fun e => @noConfusion False (C fa) (C fb) e h))
//!   (isTrue  h => isTrue  (@congrArg T X fa fb C h))
//! ```
//!
//! All universe levels are written explicitly so monomorphic concretization
//! leaves them untouched, and the produced term INFER-TYPES against the
//! kernel-generated `X.casesOn` / `X.noConfusion` — no `sorry`, empty
//! `axiom_deps`.

use crate::infer::ElabCtx;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::{SurfaceCtor, SurfaceExpr};

/// A constructor's non-recursive fields, each with its elaborated type and a
/// closed `DecidableEq fieldTy` instance.
struct FieldedCtor {
    /// Fully-qualified ctor name (`X.rgb`).
    name: Name,
    /// (fieldTy, decEqInst) per field, in declaration order.
    fields: Vec<(Expr, Expr)>,
}

impl<'a> ElabCtx<'a> {
    /// Build a real `DecidableEq` decision body for a monomorphic multi-ctor
    /// inductive whose ctor fields are all non-recursive with closed
    /// `DecidableEq` instances. Returns `None` (caller falls back) otherwise.
    ///
    /// `ind_type` is `X`. `a`/`b` are referenced as `bvar 1` / `bvar 0` inside
    /// the outer `λ (a b : X)` the caller wraps around the returned body.
    pub(super) fn build_decidable_eq_fielded(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        ctors: &[SurfaceCtor],
    ) -> Option<Expr> {
        let short = ind_name
            .to_string()
            .rsplit('.')
            .next()
            .unwrap_or("")
            .to_string();

        // Analyze every ctor; bail if any field is recursive or lacks a closed
        // `DecidableEq` instance. Ctors may carry any number of NON-recursive
        // fields: the per-field decision is folded through a nested
        // `Decidable.casesOn`, with the forward (isTrue) direction built by a
        // chained `congrArg`/`Eq.trans` over the partially-applied constructor
        // and the backward (isFalse) direction by `noConfusion` (Track P). A
        // nullary ctor (zero fields) is decided by `noConfusion` reflexivity.
        let mut analyzed = Vec::with_capacity(ctors.len());
        let mut any_fielded = false;
        for ctor in ctors {
            let fc = self.analyze_fielded_ctor(ind_name, &short, ind_type, ctor)?;
            if !fc.fields.is_empty() {
                any_fielded = true;
            }
            analyzed.push(fc);
        }
        // All-nullary enums are handled by the dedicated enum path; this builder
        // targets the case where at least one ctor carries a field.
        if !any_fielded {
            return None;
        }

        let level_one = Level::succ(Level::zero());
        let cases_on = Name::from_string(&format!("{ind_name}.casesOn"));
        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![level_one.clone()]);

        let a_ref = Expr::bvar(1);
        let b_ref = Expr::bvar(0);

        // Outer motive: `fun a' : X => Decidable (@Eq X a' b)`.
        // Inside the motive lambda a' = bvar 0, and b (outer bvar 0) lifts to 1.
        let outer_motive = {
            let eq_prop = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), ind_type.clone()), Expr::bvar(0)),
                Expr::bvar(1),
            );
            Expr::lam(
                BinderInfo::Default,
                ind_type.clone(),
                Expr::app(decidable.clone(), eq_prop),
            )
        };

        // Outer minors: one per ctor of `a`.
        let mut outer_minors = Vec::with_capacity(analyzed.len());
        for fc_a in &analyzed {
            let minor =
                self.build_outer_minor(ind_name, ind_type, &cases_on, &analyzed, fc_a, &b_ref);
            outer_minors.push(minor);
        }

        // `X.casesOn.{1} outer_motive a outer_minor..`
        // Lean-faithful casesOn order: motive, (indices,) major, then minors.
        let mut outer = Expr::const_(cases_on, vec![level_one]);
        outer = Expr::app(outer, outer_motive);
        outer = Expr::app(outer, a_ref);
        for m in outer_minors {
            outer = Expr::app(outer, m);
        }
        Some(outer)
    }

    /// Analyze one constructor into its non-recursive fields + DecidableEq
    /// instances. Returns `None` if any field is recursive (mentions the
    /// inductive) or has no closed `DecidableEq` instance.
    fn analyze_fielded_ctor(
        &mut self,
        ind_name: &Name,
        short: &str,
        ind_type: &Expr,
        ctor: &SurfaceCtor,
    ) -> Option<FieldedCtor> {
        let mut fields = Vec::new();
        self.collect_decidable_fields(short, ind_type, &ctor.ty, &mut fields)?;
        // The kernel registers each constructor under the FULLY-QUALIFIED
        // inductive name (`{ind_name}.{ctor}`, e.g. `TrustIr.Permission.owned`),
        // see `elab_inductive` constructor registration. Building the name from
        // the short inductive segment (`Permission.owned`) yields an unknown
        // constant and the whole instance fails the kernel check. Use the full
        // `ind_name`; `short` stays only for surface-type recursion detection.
        Some(FieldedCtor {
            name: Name::from_string(&format!("{ind_name}.{}", ctor.name)),
            fields,
        })
    }

    /// Peel a ctor's surface telescope; for each field elaborate its type and
    /// resolve a closed `DecidableEq` instance.
    fn collect_decidable_fields(
        &mut self,
        short: &str,
        ind_type: &Expr,
        surf: &SurfaceExpr,
        out: &mut Vec<(Expr, Expr)>,
    ) -> Option<()> {
        match surf {
            SurfaceExpr::Arrow(_, d, c) => {
                out.push(self.field_decidable(short, ind_type, d)?);
                self.collect_decidable_fields(short, ind_type, c, out)
            }
            SurfaceExpr::Pi(span, binders, body) => {
                let b = binders.first()?;
                let t = b.ty.as_ref()?;
                out.push(self.field_decidable(short, ind_type, t)?);
                if binders.len() > 1 {
                    let tail = SurfaceExpr::Pi(*span, binders[1..].to_vec(), body.clone());
                    self.collect_decidable_fields(short, ind_type, &tail, out)
                } else {
                    self.collect_decidable_fields(short, ind_type, body, out)
                }
            }
            SurfaceExpr::Paren(_, inner) => {
                self.collect_decidable_fields(short, ind_type, inner, out)
            }
            _ => Some(()),
        }
    }

    /// Elaborate a field type and resolve a closed `DecidableEq fieldTy`, or
    /// `None` if recursive / unresolved.
    fn field_decidable(
        &mut self,
        short: &str,
        ind_type: &Expr,
        ty: &SurfaceExpr,
    ) -> Option<(Expr, Expr)> {
        // Reject any field that mentions the inductive itself (recursive
        // DecidableEq needs structural recursion not handled here).
        if surface_mentions(ty, short) {
            return None;
        }
        let elaborated = self.elaborate(ty).ok()?;
        if expr_mentions_const(&elaborated, ind_type) {
            return None;
        }
        let class = Name::from_string("DecidableEq");
        let goal = Expr::app(self.mk_const(&class), elaborated.clone());
        let inst = self.resolve_instance(&goal)?;
        if inst.has_fvar_quick() || self.has_metavars(&inst) {
            return None;
        }
        Some((elaborated, inst))
    }

    /// Outer minor for ctor `fc_a`: bind `a`'s fields, then `casesOn` on `b`.
    fn build_outer_minor(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        cases_on: &Name,
        all_ctors: &[FieldedCtor],
        fc_a: &FieldedCtor,
        b_ref: &Expr,
    ) -> Expr {
        let level_one = Level::succ(Level::zero());
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![level_one.clone()]);
        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);

        // Fresh fvars for a's fields.
        let a_fvars: Vec<FVarId> = fc_a.fields.iter().map(|_| self.fresh_fvar()).collect();
        let ctor_a = Expr::const_(fc_a.name.clone(), vec![]);
        let a_applied = apply_fields(&ctor_a, &a_fvars);

        // Inner motive: `fun b' : X => Decidable (@Eq X (Cᵢ fa..) b')`.
        let inner_motive = {
            let eq_prop = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), ind_type.clone()),
                    a_applied.clone(),
                ),
                Expr::bvar(0),
            );
            Expr::lam(
                BinderInfo::Default,
                ind_type.clone(),
                Expr::app(decidable.clone(), eq_prop),
            )
        };

        // Inner minors over b's ctor.
        let mut inner_minors = Vec::with_capacity(all_ctors.len());
        for fc_b in all_ctors {
            let minor = if fc_b.name == fc_a.name {
                self.build_same_ctor_decision(ind_name, ind_type, fc_a, &a_fvars, &a_applied)
            } else {
                self.build_diff_ctor_decision(ind_name, ind_type, fc_a, fc_b, &a_applied)
            };
            inner_minors.push(minor);
        }

        // `X.casesOn.{1} inner_motive b inner_minor..`
        // Lean-faithful casesOn order: motive, (indices,) major, then minors.
        let mut inner = Expr::const_(cases_on.clone(), vec![level_one]);
        inner = Expr::app(inner, inner_motive);
        inner = Expr::app(inner, b_ref.clone());
        for m in inner_minors {
            inner = Expr::app(inner, m);
        }

        // Abstract a's fields back into lambdas (innermost-first).
        let mut body = inner;
        for k in (0..a_fvars.len()).rev() {
            body = body.abstract_fvar(a_fvars[k]);
            body = Expr::lam(BinderInfo::Default, fc_a.fields[k].0.clone(), body);
        }
        body
    }

    /// Inner minor when `b`'s ctor differs from `a`'s: bind `b`'s fields and
    /// return `isFalse` witnessed by `noConfusion` (distinct ctors ⇒ `False`).
    fn build_diff_ctor_decision(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        _fc_a: &FieldedCtor,
        fc_b: &FieldedCtor,
        a_applied: &Expr,
    ) -> Expr {
        let no_conf = Name::from_string(&format!("{ind_name}.noConfusion"));
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        let b_fvars: Vec<FVarId> = fc_b.fields.iter().map(|_| self.fresh_fvar()).collect();
        let ctor_b = Expr::const_(fc_b.name.clone(), vec![]);
        let b_applied = apply_fields(&ctor_b, &b_fvars);

        // eq_prop : @Eq X (Cᵢ fa..) (Cⱼ fb..)
        let eq_prop = Expr::app(
            Expr::app(Expr::app(eq_const, ind_type.clone()), a_applied.clone()),
            b_applied.clone(),
        );

        // neg : eq_prop -> False  ==  fun e => @X.noConfusion.{0} False (Cᵢfa) (Cⱼfb) e
        let e_fvar = self.fresh_fvar();
        let no_conf_call = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(no_conf, vec![Level::zero()]),
                        false_const.clone(),
                    ),
                    a_applied.clone(),
                ),
                b_applied.clone(),
            ),
            Expr::fvar(e_fvar),
        );
        let neg = Expr::lam(
            BinderInfo::Default,
            eq_prop.clone(),
            no_conf_call.abstract_fvar(e_fvar),
        );

        // @Decidable.isFalse eq_prop neg
        let mut body = Expr::app(Expr::app(is_false, eq_prop), neg);

        // Abstract b's fields.
        for k in (0..b_fvars.len()).rev() {
            body = body.abstract_fvar(b_fvars[k]);
            body = Expr::lam(BinderInfo::Default, fc_b.fields[k].0.clone(), body);
        }
        body
    }

    /// Inner minor when `b`'s ctor equals `a`'s: bind `b`'s fields and dispatch
    /// per-field `DecidableEq`, threading the decisions through `congrArg` /
    /// `noConfusion`.
    fn build_same_ctor_decision(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        fc: &FieldedCtor,
        a_fvars: &[FVarId],
        a_applied: &Expr,
    ) -> Expr {
        let b_fvars: Vec<FVarId> = fc.fields.iter().map(|_| self.fresh_fvar()).collect();
        let ctor_c = Expr::const_(fc.name.clone(), vec![]);
        let b_applied = apply_fields(&ctor_c, &b_fvars);

        // Nullary ctor: `a` and `b` are the same closed constructor constant, so
        // the equality is reflexive — `isTrue (Eq.refl X C)`.
        if fc.fields.is_empty() {
            let level_one = Level::succ(Level::zero());
            let whole_eq = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![level_one.clone()]),
                        ind_type.clone(),
                    ),
                    a_applied.clone(),
                ),
                b_applied.clone(),
            );
            let refl = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq.refl"), vec![level_one]),
                    ind_type.clone(),
                ),
                a_applied.clone(),
            );
            return Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                    whole_eq,
                ),
                refl,
            );
        }

        // Decide field-by-field, folding from the LAST field inward so the
        // innermost decision yields `isTrue (refl)`-style equality for the whole
        // ctor application and outer fields wrap with congrArg / noConfusion.
        let decision = self.fold_field_decisions(
            ind_name, ind_type, fc, &ctor_c, a_fvars, &b_fvars, a_applied, &b_applied,
        );

        // Abstract b's fields.
        let mut body = decision;
        for k in (0..b_fvars.len()).rev() {
            body = body.abstract_fvar(b_fvars[k]);
            body = Expr::lam(BinderInfo::Default, fc.fields[k].0.clone(), body);
        }
        body
    }

    /// Build `Decidable (Cᵢ a_fields.. = Cᵢ b_fields..)` by deciding each field
    /// in turn and combining via a chained `congrArg`/`Eq.trans` (isTrue forward
    /// direction) and `noConfusion` (isFalse backward direction).
    ///
    /// For N fields this is a nested `Decidable.casesOn`: decide field 0; on
    /// `isTrue` recurse into field 1, …; on `isFalse` short-circuit to
    /// `isFalse` of the whole-ctor equality via `noConfusion`. When ALL fields
    /// decide equal, the accumulated field-equality proofs `h₀ : a₀=b₀ … h_{n-1}`
    /// are folded through congruence to produce `C a.. = C b..`. The whole-ctor
    /// motive is constant in the bound decision/proof, so no de-Bruijn shifting
    /// of the result type is needed.
    #[allow(clippy::too_many_arguments)]
    fn fold_field_decisions(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        fc: &FieldedCtor,
        ctor_c: &Expr,
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
        a_applied: &Expr,
        b_applied: &Expr,
    ) -> Expr {
        debug_assert!(!fc.fields.is_empty(), "nullary handled by caller");
        // Accumulate the field-equality proof fvars (one per already-decided
        // field) as we descend; the base builds the forward congruence chain.
        let heq_fvars: Vec<FVarId> = Vec::new();
        self.decide_from_field(
            ind_name, ind_type, fc, ctor_c, a_fvars, b_fvars, a_applied, b_applied, 0, &heq_fvars,
        )
    }

    /// Recursive driver: produce `Decidable (C a.. = C b..)` assuming fields
    /// `0..k` already decided equal with proofs in `heq_fvars`. At `k == n`,
    /// all fields are equal and we emit `isTrue` of the congruence chain;
    /// otherwise we `Decidable.casesOn` the decision for field `k`.
    #[allow(clippy::too_many_arguments)]
    fn decide_from_field(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        fc: &FieldedCtor,
        ctor_c: &Expr,
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
        a_applied: &Expr,
        b_applied: &Expr,
        k: usize,
        heq_fvars: &[FVarId],
    ) -> Expr {
        let level_one = Level::succ(Level::zero());

        // whole_eq : @Eq X (C a..) (C b..) — invariant across the recursion.
        let whole_eq = mk_eq(&level_one, ind_type, a_applied, b_applied);

        if k == fc.fields.len() {
            // All fields equal: isTrue (congruence chain h₀ .. h_{n-1}).
            let proof = self.build_congr_chain(
                &level_one, ind_type, fc, ctor_c, a_fvars, b_fvars, heq_fvars,
            );
            let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
            return Expr::app(Expr::app(is_true, whole_eq), proof);
        }

        let (fty, finst) = &fc.fields[k];
        let fa = Expr::fvar(a_fvars[k]);
        let fb = Expr::fvar(b_fvars[k]);

        // field_eq_k : @Eq T_k a_k b_k.
        let field_eq = mk_eq(&level_one, fty, &fa, &fb);
        // dec_k : Decidable field_eq_k  ==  decEqInst a_k b_k.
        let dec = Expr::app(Expr::app(finst.clone(), fa.clone()), fb.clone());

        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
        let dec_cases_on = Name::from_string("Decidable.casesOn");
        let dec_field = Expr::app(decidable.clone(), field_eq.clone());

        // motive: fun (_ : Decidable field_eq_k) => Decidable whole_eq.
        // whole_eq is closed wrt this binder.
        let motive = Expr::lam(
            BinderInfo::Default,
            dec_field,
            Expr::app(decidable.clone(), whole_eq.clone()),
        );

        // isFalse minor: fun (hne : a_k = b_k -> False) =>
        //   isFalse whole_eq (fun e => noConfusion False (C a) (C b) e (fun e₀..e_{n-1} => hne e_k))
        let isfalse_minor = self.build_isfalse_minor(
            ind_name, fc, a_fvars, b_fvars, a_applied, b_applied, &whole_eq, &field_eq, k,
        );

        // isTrue minor: fun (h_k : a_k = b_k) => decide_from_field(k+1, heq ++ [h_k]).
        let istrue_minor = {
            let h_fvar = self.fresh_fvar();
            let mut next_heqs = heq_fvars.to_vec();
            next_heqs.push(h_fvar);
            let body = self.decide_from_field(
                ind_name,
                ind_type,
                fc,
                ctor_c,
                a_fvars,
                b_fvars,
                a_applied,
                b_applied,
                k + 1,
                &next_heqs,
            );
            Expr::lam(
                BinderInfo::Default,
                field_eq.clone(),
                body.abstract_fvar(h_fvar),
            )
        };

        // @Decidable.casesOn.{1} (p := field_eq) (motive := …) dec isFalse isTrue.
        // Lean-faithful casesOn order: motive, (indices,) major, then minors.
        let mut cases = Expr::const_(dec_cases_on, vec![level_one]);
        cases = Expr::app(cases, field_eq);
        cases = Expr::app(cases, motive);
        cases = Expr::app(cases, dec);
        cases = Expr::app(cases, isfalse_minor);
        cases = Expr::app(cases, istrue_minor);
        cases
    }

    /// `isFalse` minor for a field-`k` mismatch: `fun (hne : a_k=b_k -> False) =>
    /// isFalse whole_eq (fun e => noConfusion False (C a) (C b) e (fun e₀..e_{n-1} => hne e_k))`.
    /// The N-field `noConfusion` evidence is `(a₀=b₀ -> … -> a_{n-1}=b_{n-1} -> P) -> P`;
    /// we feed it a continuation that ignores all but the `k`-th equality and
    /// applies `hne` to reach `False`.
    #[allow(clippy::too_many_arguments)]
    fn build_isfalse_minor(
        &mut self,
        ind_name: &Name,
        fc: &FieldedCtor,
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
        a_applied: &Expr,
        b_applied: &Expr,
        whole_eq: &Expr,
        field_eq_k: &Expr,
        k: usize,
    ) -> Expr {
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        let no_conf = Name::from_string(&format!("{ind_name}.noConfusion"));
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let level_one = Level::succ(Level::zero());

        let hne_fvar = self.fresh_fvar();
        let e_fvar = self.fresh_fvar();

        // Continuation fed to noConfusion: fun (e₀:a₀=b₀) … (e_{n-1}:a_{n-1}=b_{n-1}) => hne e_k.
        let ek_fvars: Vec<FVarId> = fc.fields.iter().map(|_| self.fresh_fvar()).collect();
        let mut cont = Expr::app(Expr::fvar(hne_fvar), Expr::fvar(ek_fvars[k]));
        for (i, (fty, _)) in fc.fields.iter().enumerate().rev() {
            cont = cont.abstract_fvar(ek_fvars[i]);
            // e_i : @Eq T_i a_i b_i, using the captured a_i/b_i field fvars.
            let ei_ty = mk_eq(
                &level_one,
                fty,
                &Expr::fvar(a_fvars[i]),
                &Expr::fvar(b_fvars[i]),
            );
            cont = Expr::lam(BinderInfo::Default, ei_ty, cont);
        }

        // noConfusion.{0} False (C a) (C b) e cont : False
        let nc = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(no_conf, vec![Level::zero()]),
                        false_const.clone(),
                    ),
                    a_applied.clone(),
                ),
                b_applied.clone(),
            ),
            Expr::fvar(e_fvar),
        );
        let nc_applied = Expr::app(nc, cont);
        // fun e : whole_eq => nc_applied
        let neg = Expr::lam(
            BinderInfo::Default,
            whole_eq.clone(),
            nc_applied.abstract_fvar(e_fvar),
        );
        // @Decidable.isFalse whole_eq neg
        let body = Expr::app(Expr::app(is_false, whole_eq.clone()), neg);
        // fun hne : (a_k=b_k -> False) => body
        let hne_ty = Expr::arrow(field_eq_k.clone(), false_const);
        Expr::lam(BinderInfo::Default, hne_ty, body.abstract_fvar(hne_fvar))
    }

    /// Build `C a₀..a_{n-1} = C b₀..b_{n-1}` from field-equality proofs
    /// `h₀ : a₀=b₀ … h_{n-1}` via a chain of `congrArg` over the constructor,
    /// substituting one field at a time and stitching with `Eq.trans`.
    ///
    /// Step `k` replaces field `k` (with `b₀..b_{k-1}` already substituted and
    /// `a_{k+1}..a_{n-1}` still present):
    /// ```text
    /// congrArg T_k X a_k b_k (fun x => C b₀..b_{k-1} x a_{k+1}..a_{n-1}) h_k
    ///   : C b₀..b_{k-1} a_k a_{k+1}.. = C b₀..b_{k-1} b_k a_{k+1}..
    /// ```
    #[allow(clippy::too_many_arguments)]
    fn build_congr_chain(
        &mut self,
        level_one: &Level,
        ind_type: &Expr,
        fc: &FieldedCtor,
        ctor_c: &Expr,
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
        heq_fvars: &[FVarId],
    ) -> Expr {
        let n = fc.fields.len();
        let congr_arg = Name::from_string("congrArg");

        // `mid(j)` is the constructor applied with fields `b₀..b_{j-1}` then
        // `a_j..a_{n-1}` — the intermediate point after substituting the first
        // `j` fields. `mid(0) = C a..`, `mid(n) = C b..`.
        let mid = |j: usize| -> Expr {
            let mut applied = ctor_c.clone();
            for i in 0..n {
                let arg = if i < j {
                    Expr::fvar(b_fvars[i])
                } else {
                    Expr::fvar(a_fvars[i])
                };
                applied = Expr::app(applied, arg);
            }
            applied
        };

        // Fold `Eq.trans` over per-field `congrArg` steps; step `k` carries
        // `mid(k) = mid(k+1)`.
        let mut acc: Option<Expr> = None;
        for k in 0..n {
            let (fty, _) = &fc.fields[k];
            let fa = Expr::fvar(a_fvars[k]);
            let fb = Expr::fvar(b_fvars[k]);
            let h_k = Expr::fvar(heq_fvars[k]);

            // f_k := fun (x : T_k) => C b₀..b_{k-1} x a_{k+1}..a_{n-1}.
            let x_fvar = self.fresh_fvar();
            let mut applied = ctor_c.clone();
            for j in 0..n {
                let arg = if j < k {
                    Expr::fvar(b_fvars[j])
                } else if j == k {
                    Expr::fvar(x_fvar)
                } else {
                    Expr::fvar(a_fvars[j])
                };
                applied = Expr::app(applied, arg);
            }
            let f_k = Expr::lam(
                BinderInfo::Default,
                fty.clone(),
                applied.abstract_fvar(x_fvar),
            );

            // @congrArg.{1,1} T_k X a_k b_k f_k h_k : mid(k) = mid(k+1).
            let step = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::const_(
                                        congr_arg.clone(),
                                        vec![level_one.clone(), level_one.clone()],
                                    ),
                                    fty.clone(),
                                ),
                                ind_type.clone(),
                            ),
                            fa,
                        ),
                        fb,
                    ),
                    f_k,
                ),
                h_k,
            );

            acc = Some(match acc {
                None => step,
                Some(prev) => {
                    // prev : mid(0) = mid(k); step : mid(k) = mid(k+1).
                    // @Eq.trans.{1} X mid(0) mid(k) mid(k+1) prev step.
                    eq_trans(
                        level_one,
                        ind_type,
                        &mid(0),
                        &mid(k),
                        &mid(k + 1),
                        prev,
                        step,
                    )
                }
            });
        }
        acc.expect("non-empty fields")
    }
}

/// `@Eq.trans.{u} α x y z p q : x = z` with all points supplied explicitly.
fn eq_trans(level: &Level, ty: &Expr, x: &Expr, y: &Expr, z: &Expr, p: Expr, q: Expr) -> Expr {
    let trans = Expr::const_(Name::from_string("Eq.trans"), vec![level.clone()]);
    let mut e = Expr::app(trans, ty.clone());
    e = Expr::app(e, x.clone());
    e = Expr::app(e, y.clone());
    e = Expr::app(e, z.clone());
    e = Expr::app(e, p);
    e = Expr::app(e, q);
    e
}

/// `@Eq.{u} α a b`.
fn mk_eq(level: &Level, ty: &Expr, a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
                ty.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// `head a₀ a₁ …` applied over a list of field fvars.
fn apply_fields(head: &Expr, fvars: &[FVarId]) -> Expr {
    let mut e = head.clone();
    for f in fvars {
        e = Expr::app(e, Expr::fvar(*f));
    }
    e
}

/// Whether a surface type mentions identifier `name` (used to reject recursive
/// fields, where DecidableEq would need structural recursion).
fn surface_mentions(expr: &SurfaceExpr, name: &str) -> bool {
    match expr {
        SurfaceExpr::Ident(_, n) => n == name,
        SurfaceExpr::App(_, h, args) => {
            surface_mentions(h, name) || args.iter().any(|a| surface_mentions(&a.expr, name))
        }
        SurfaceExpr::Arrow(_, l, r) => surface_mentions(l, name) || surface_mentions(r, name),
        SurfaceExpr::Paren(_, i) | SurfaceExpr::Ascription(_, i, _) => surface_mentions(i, name),
        _ => false,
    }
}

/// Whether an elaborated expr references the inductive's own type constant.
fn expr_mentions_const(expr: &Expr, ind_type: &Expr) -> bool {
    let target = match ind_type.kind() {
        ExprKind::Const(n, _) => n.clone(),
        _ => return false,
    };
    fn go(e: &Expr, target: &Name) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => n == target,
            ExprKind::App(f, a) => go(f, target) || go(a, target),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => go(t, target) || go(b, target),
            _ => false,
        }
    }
    go(expr, &target)
}

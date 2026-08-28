// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Kernel-proved `List.reverse_reverse` and `List.map_map` simp lemmas.
//!
//! Both are real `Declaration::Theorem`s with hand-built `List.rec` proof
//! terms routed through the checked `add_decl` path (NO `sorry`, NO axiom, NO
//! structural/unchecked insertion). They back the default-simp-set rewrites
//! that close the everyday-battery goals `xs.reverse.reverse = xs` and
//! `(xs.map f).map g = xs.map (g ∘ f)`:
//!
//! ```text
//! List.reverse_reverse : {α : Type u} → (xs : List α) →
//!     @List.reverse α (@List.reverse α xs) = xs
//! List.map_map : {α : Type u} {β : Type v} {γ : Type w} →
//!     (g : β → γ) → (f : α → β) → (xs : List α) →
//!     @List.map β γ g (@List.map α β f xs)
//!       = @List.map α γ (fun (x : α) => g (f x)) xs
//! ```
//!
//! `List.map_map`'s fused function is spelled as the raw lambda
//! `fun x => g (f x)`, NOT `Function.comp g f`: Clean's elaborator desugars
//! every applied `∘` to exactly that lambda (`infer/mod.rs`, the
//! `Function.comp` surface-App arm), so this statement is precisely how
//! Clean elaborates the Lean-surface statement `(xs.map f).map g =
//! xs.map (g ∘ f)` — and the simp rewrite's RHS lands syntactically equal to
//! the goal's own RHS.
//!
//! Proof terms:
//!
//! - `List.reverse_reverse`: `List.reverse` is `reverseAux · []`
//!   (`data_collection_ops.rs`), so the induction is carried by the
//!   accumulator-generalized auxiliary
//!   `∀ (l r : List α), reverseAux (reverseAux l r) [] = reverseAux r l`,
//!   inlined as a single `List.rec.{0,u}` term (motive is the `∀ r, …` Prop):
//!   * nil : `fun r => Eq.refl (List α) (reverseAux r [])` — the motive at
//!     `[]` ι-reduces its LHS `reverseAux (reverseAux [] r) []` to
//!     `reverseAux r []`, the RHS literally.
//!   * cons: `fun a l ih r => ih (a :: r)` — both ends are pure ι:
//!     `reverseAux (a::l) r ↦ reverseAux l (a::r)` inside the LHS, and the
//!     ih's RHS `reverseAux (a::r) l ↦ reverseAux r (a::l)` is the goal RHS.
//!   The theorem value applies the recursion at `(xs, [])`:
//!   `reverse (reverse xs)` δ-reduces to `reverseAux (reverseAux xs []) []`
//!   and `reverseAux [] xs` ι-reduces to `xs`.
//!
//! - `List.map_map`: direct `List.rec.{0,u}` on `xs` with motive
//!   `fun l => map g (map f l) = map (fun x => g (f x)) l`:
//!   * nil : `Eq.refl (List γ) (@List.nil γ)` (both sides ι-reduce to `[]`).
//!   * cons: `congrArg (fun t => (g (f x)) :: t) ih` — the motive at
//!     `x :: l` ι/β-reduces both sides to `(g (f x)) :: …`, matching the
//!     congruence exactly (the same `congrArg` step `List.append_nil` and
//!     `List.length_append` already use).
//!
//! Transitive axiom closure for both: `List.rec` (recursor), `Eq.refl`,
//! `congrArg` — all FOUNDATIONAL; a genuine 0-domain-axiom proof pair.
//!
//! SOUNDNESS: every value goes through the checked `add_decl`, so the kernel
//! re-verifies each proof term against its declared type; any mis-assembly
//! fails closed. IMPORT MODE (`suppress_lossy_structure_stubs`): both
//! theorems state goals over the gated `List.reverseAux`/`List.reverse`/
//! `List.map` seeds, so they are gated with that cluster exactly like the
//! sibling `List.append_nil`/`List.length_*` lemmas — the genuine olean
//! theorems import through the checked path instead.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `List.reverse_reverse` and `List.map_map` (kernel-proved,
    /// axiom-free). Idempotent; a no-op in import mode (see module docs).
    ///
    /// REQUIRES: called from `init_list_ops` after the `List.reverseAux`/
    /// `List.reverse`/`List.map` seeds are registered (non-import mode).
    /// ENSURES: on success (non-import mode), both theorems are present and
    /// were verified by the checked `add_decl` path.
    pub(crate) fn init_list_reverse_map_lemmas(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        // Eq / Eq.refl / congrArg (idempotent).
        self.init_eq()?;
        self.register_list_reverse_reverse()?;
        self.register_list_map_map()?;
        Ok(())
    }

    /// `List.reverse_reverse.{u} : {α : Type u} → (xs : List α) →
    ///   @List.reverse α (@List.reverse α xs) = xs`
    ///
    /// value:
    /// ```text
    /// fun {α} (xs) =>
    ///   (@List.rec.{0,u} α
    ///      (fun (l : List α) => (r : List α) →
    ///         @Eq (List α) (reverseAux (reverseAux l r) []) (reverseAux r l))
    ///      (fun (r : List α) => @Eq.refl (List α) (reverseAux r []))
    ///      (fun (a : α) (l : List α) (ih : …) (r : List α) => ih (a :: r))
    ///      xs)
    ///   (@List.nil α)
    /// ```
    fn register_list_reverse_reverse(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("List.reverse_reverse"))
            .is_some()
        {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_lvl = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_lvl.clone())));
        let list_const = Expr::const_(Name::from_string("List"), vec![u_lvl.clone()]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_lvl.clone()]);
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_lvl.clone()]);
        let reverse_const = Expr::const_(Name::from_string("List.reverse"), vec![u_lvl.clone()]);
        let raux_const = Expr::const_(Name::from_string("List.reverseAux"), vec![u_lvl.clone()]);
        // Carrier `List α : Type u = Sort (u+1)`.
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_lvl.clone())]);
        let eq_refl_const = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(u_lvl.clone())],
        );

        let list_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
        let nil_of = |a: &Expr| Expr::app(list_nil.clone(), a.clone());
        let raux_of =
            |a: &Expr, l: Expr, r: Expr| Expr::apps(raux_const.clone(), [a.clone(), l, r]);
        let rev_of = |a: &Expr, l: Expr| Expr::apps(reverse_const.clone(), [a.clone(), l]);
        let eq_of =
            |a: &Expr, lhs: Expr, rhs: Expr| Expr::apps(eq_const.clone(), [list_of(a), lhs, rhs]);
        // The auxiliary motive body at `l`, `r`:
        //   reverseAux (reverseAux l r) [] = reverseAux r l
        let aux_eq_of = |a: &Expr, l: Expr, r: Expr| {
            eq_of(
                a,
                raux_of(a, raux_of(a, l.clone(), r.clone()), nil_of(a)),
                raux_of(a, r, l),
            )
        };

        // Type: {α : Type u} → (xs : List α) → reverse (reverse xs) = xs
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (xs_id, xs) = b.fresh_local(list_of(&alpha));
            let concl = eq_of(
                &alpha,
                rev_of(&alpha, rev_of(&alpha, xs.clone())),
                xs.clone(),
            );
            let e = b.mk_pi(xs_id, BinderInfo::Default, list_of(&alpha), concl);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = list_of(&alpha);

            // motive : fun (l : List α) => (r : List α) → aux_eq l r   (→ Prop)
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (l_id, l) = c.fresh_local(list_alpha.clone());
                let (r_id, r) = c.fresh_local(list_alpha.clone());
                let concl = aux_eq_of(&alpha, l.clone(), r.clone());
                let pi = c.mk_pi(r_id, BinderInfo::Default, list_alpha.clone(), concl);
                let lam = c.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), pi);
                c.finish_child(lam)
            };

            // nil case : fun (r : List α) => Eq.refl (List α) (reverseAux r [])
            // (motive at `[]` ι-reduces its LHS to exactly `reverseAux r []`).
            let nil_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (r_id, r) = c.fresh_local(list_alpha.clone());
                let body = Expr::apps(
                    eq_refl_const.clone(),
                    [
                        list_alpha.clone(),
                        raux_of(&alpha, r.clone(), nil_of(&alpha)),
                    ],
                );
                let lam = c.mk_lam(r_id, BinderInfo::Default, list_alpha.clone(), body);
                c.finish_child(lam)
            };

            // cons case : fun (a : α) (l : List α)
            //   (ih : (r : List α) → aux_eq l r) (r : List α) => ih (a :: r)
            // — both sides of `ih (a :: r)`'s type ι-reduce to the motive at
            // `a :: l` applied to `r` (see module docs).
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let (l_id, l) = c.fresh_local(list_alpha.clone());
                let ih_ty = {
                    let (r0_id, r0) = c.fresh_local(list_alpha.clone());
                    let concl = aux_eq_of(&alpha, l.clone(), r0.clone());
                    c.mk_pi(r0_id, BinderInfo::Default, list_alpha.clone(), concl)
                };
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let (r_id, r) = c.fresh_local(list_alpha.clone());
                let a_cons_r = Expr::apps(list_cons.clone(), [alpha.clone(), a.clone(), r.clone()]);
                let body = Expr::app(ih.clone(), a_cons_r);
                let lam = c.mk_lam(r_id, BinderInfo::Default, list_alpha.clone(), body);
                let lam = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
                let lam = c.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), lam);
                let lam = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), lam);
                c.finish_child(lam)
            };

            // (List.rec.{0, u} α motive nil_case cons_case xs) (@List.nil α)
            let list_rec_prop = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), u_lvl.clone()],
            );
            let (xs_id, xs) = b.fresh_local(list_alpha.clone());
            let rec_app = Expr::apps(
                list_rec_prop,
                [alpha.clone(), motive, nil_case, cons_case, xs.clone()],
            );
            let body = Expr::app(rec_app, nil_of(&alpha));
            let e = b.mk_lam(xs_id, BinderInfo::Default, list_alpha.clone(), body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.reverse_reverse"),
            level_params: vec![u],
            type_: ty,
            value,
        })
    }

    /// `List.map_map.{u,v,w} : {α : Type u} {β : Type v} {γ : Type w} →
    ///   (g : β → γ) → (f : α → β) → (xs : List α) →
    ///   @List.map β γ g (@List.map α β f xs)
    ///     = @List.map α γ (fun (x : α) => g (f x)) xs`
    ///
    /// value: `List.rec.{0,u}` on `xs`; nil closes by `Eq.refl (List γ) []`,
    /// cons is `congrArg (fun (t : List γ) => (g (f x)) :: t) ih`.
    fn register_list_map_map(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("List.map_map")).is_some() {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let w = Name::from_string("w");
        let u_lvl = Level::param(u.clone());
        let v_lvl = Level::param(v.clone());
        let w_lvl = Level::param(w.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_lvl.clone())));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(v_lvl.clone())));
        let type_w = Expr::from_kind(ExprKind::Sort(Level::succ(w_lvl.clone())));
        let list_u = Expr::const_(Name::from_string("List"), vec![u_lvl.clone()]);
        let list_w = Expr::const_(Name::from_string("List"), vec![w_lvl.clone()]);
        let list_nil_w = Expr::const_(Name::from_string("List.nil"), vec![w_lvl.clone()]);
        let list_cons_w = Expr::const_(Name::from_string("List.cons"), vec![w_lvl.clone()]);
        let map_uv = Expr::const_(
            Name::from_string("List.map"),
            vec![u_lvl.clone(), v_lvl.clone()],
        );
        let map_vw = Expr::const_(
            Name::from_string("List.map"),
            vec![v_lvl.clone(), w_lvl.clone()],
        );
        let map_uw = Expr::const_(
            Name::from_string("List.map"),
            vec![u_lvl.clone(), w_lvl.clone()],
        );
        // Carrier `List γ : Type w = Sort (w+1)`.
        let eq_w = Expr::const_(Name::from_string("Eq"), vec![Level::succ(w_lvl.clone())]);
        let eq_refl_w = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(w_lvl.clone())],
        );
        // congrArg.{w+1, w+1} : {α β : Sort (w+1)} {a₁ a₂ : α} (f : α → β) →
        //   a₁ = a₂ → f a₁ = f a₂   (here α = β = List γ).
        let congr_arg_w = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(w_lvl.clone()), Level::succ(w_lvl.clone())],
        );

        // Conclusion at `alpha`/`beta`/`gamma`/`g`/`f` for list `l`:
        //   map g (map f l) = map (fun x => g (f x)) l
        // `comp_lam` is the caller-built `fun (x : α) => g (f x)`.
        let concl_of = |beta: &Expr,
                        gamma: &Expr,
                        g: &Expr,
                        f: &Expr,
                        alpha: &Expr,
                        comp_lam: &Expr,
                        l: Expr| {
            let list_gamma = Expr::app(list_w.clone(), gamma.clone());
            let inner = Expr::apps(
                map_uv.clone(),
                [alpha.clone(), beta.clone(), f.clone(), l.clone()],
            );
            let lhs = Expr::apps(
                map_vw.clone(),
                [beta.clone(), gamma.clone(), g.clone(), inner],
            );
            let rhs = Expr::apps(
                map_uw.clone(),
                [alpha.clone(), gamma.clone(), comp_lam.clone(), l],
            );
            Expr::apps(eq_w.clone(), [list_gamma, lhs, rhs])
        };

        // Type: {α β γ} → (g : β → γ) → (f : α → β) → (xs : List α) → concl
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (gamma_id, gamma) = b.fresh_local(type_w.clone());
            let g_ty = Expr::pi(BinderInfo::Default, beta.clone(), gamma.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let list_alpha = Expr::app(list_u.clone(), alpha.clone());
            let (xs_id, xs) = b.fresh_local(list_alpha.clone());
            // fun (x : α) => g (f x)
            let comp_lam = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(alpha.clone());
                let body = Expr::app(g.clone(), Expr::app(f.clone(), x));
                let lam = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), body);
                c.finish_child(lam)
            };
            let concl = concl_of(&beta, &gamma, &g, &f, &alpha, &comp_lam, xs.clone());
            let e = b.mk_pi(xs_id, BinderInfo::Default, list_alpha, concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
            let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_w.clone(), e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (gamma_id, gamma) = b.fresh_local(type_w.clone());
            let g_ty = Expr::pi(BinderInfo::Default, beta.clone(), gamma.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let list_alpha = Expr::app(list_u.clone(), alpha.clone());
            let list_gamma = Expr::app(list_w.clone(), gamma.clone());
            // fun (x : α) => g (f x)
            let comp_lam = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(alpha.clone());
                let body = Expr::app(g.clone(), Expr::app(f.clone(), x));
                let lam = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), body);
                c.finish_child(lam)
            };

            // motive : fun (l : List α) => concl l   (→ Prop)
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (l_id, l) = c.fresh_local(list_alpha.clone());
                let body = concl_of(&beta, &gamma, &g, &f, &alpha, &comp_lam, l.clone());
                let lam = c.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
                c.finish_child(lam)
            };

            // nil case : Eq.refl (List γ) (@List.nil γ)
            // (both sides of the motive at `[]` ι-reduce to `[]`).
            let nil_case = Expr::apps(
                eq_refl_w.clone(),
                [
                    list_gamma.clone(),
                    Expr::app(list_nil_w.clone(), gamma.clone()),
                ],
            );

            // cons case : fun (x : α) (l : List α) (ih : concl l) =>
            //   congrArg (List γ) (List γ) (map g (map f l))
            //     (map comp_lam l) (fun (t : List γ) => (g (f x)) :: t) ih
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(alpha.clone());
                let (l_id, l) = c.fresh_local(list_alpha.clone());
                let a1 = Expr::apps(
                    map_vw.clone(),
                    [
                        beta.clone(),
                        gamma.clone(),
                        g.clone(),
                        Expr::apps(
                            map_uv.clone(),
                            [alpha.clone(), beta.clone(), f.clone(), l.clone()],
                        ),
                    ],
                );
                let a2 = Expr::apps(
                    map_uw.clone(),
                    [alpha.clone(), gamma.clone(), comp_lam.clone(), l.clone()],
                );
                let ih_ty = Expr::apps(eq_w.clone(), [list_gamma.clone(), a1.clone(), a2.clone()]);
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                // fun (t : List γ) => cons γ (g (f x)) t
                let cons_fn = {
                    let (t_id, t) = c.fresh_local(list_gamma.clone());
                    let gfx = Expr::app(g.clone(), Expr::app(f.clone(), x.clone()));
                    let body = Expr::apps(list_cons_w.clone(), [gamma.clone(), gfx, t]);
                    c.mk_lam(t_id, BinderInfo::Default, list_gamma.clone(), body)
                };
                let body = Expr::apps(
                    congr_arg_w.clone(),
                    [list_gamma.clone(), list_gamma.clone(), a1, a2, cons_fn, ih],
                );
                let lam = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                let lam = c.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), lam);
                let lam = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), lam);
                c.finish_child(lam)
            };

            // List.rec.{0, u} α motive nil_case cons_case xs
            let list_rec_prop = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::zero(), u_lvl.clone()],
            );
            let (xs_id, xs) = b.fresh_local(list_alpha.clone());
            let body = Expr::apps(
                list_rec_prop,
                [alpha.clone(), motive, nil_case, cons_case, xs.clone()],
            );
            let e = b.mk_lam(xs_id, BinderInfo::Default, list_alpha, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(g_id, BinderInfo::Default, g_ty, e);
            let e = b.mk_lam(gamma_id, BinderInfo::Implicit, type_w.clone(), e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("List.map_map"),
            level_params: vec![u, v, w],
            type_: ty,
            value,
        })
    }
}

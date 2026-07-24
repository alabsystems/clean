// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful clean polymorphic `Definition`s for the `Fun`/`Set`-combinator HOL
//! constants whose `_def` bodies embed to closed clean terms through the
//! already-mapped `Ball`/`image`/`If`/`conj`/`@Eq` arms:
//!
//! ```text
//! Fun.fcomp       : (α→β) → (β→γ) → α → γ                    := λf g x. g (f x)
//! Fun.inj_on      : (α→β) → (α→Prop) → Prop                  := λf A. ∀x. A x → ∀y. A y → (f x = f y → x = y)
//! Fun.bij_betw    : (α→β) → (α→Prop) → (β→Prop) → Prop       := λf A B. inj_on f A ∧ (image f A = B)
//! Fun.fun_upd     : (α→β) → α → β → α → β                    := λf a b x. if x = a then b else f x
//! Fun.monotone_on : (α→Prop) → (α→α→Prop) → (β→β→Prop) → (α→β) → Prop
//!                                                            := λA le_a le_b f. ∀x. A x → ∀y. A y → (le_a x y → le_b (f x) (f y))
//! ```
//!
//! Each body is exactly what the constant's own HOL `…_def` RHS embeds to (the
//! `Set.Ball` bounded-∀ [`ball_encoding`], the [`image_encoding`], the
//! `isabelle.def.HOL.If`/`conj` def-consts, the object-level `@Eq`), so the
//! definitional axiom becomes genuinely reflexive — provable by `Eq.refl(lhs)`,
//! which the kernel accepts **iff** the def-const LHS δβ-reduces to the embedded
//! RHS. Faithful (never a `B = B` tautology): the stored proposition keeps the
//! real `C args = RHS` shape, with the def-const application and the embedded
//! body as DISTINCT operands. `bij_betw`'s body references the `inj_on`
//! def-const (registered first), matching how the `bij_betw_def` RHS's own
//! `inj_on ?f ?A` occurrence embeds. `fun_upd` routes its `if` through the SAME
//! `isabelle.def.HOL.If` head the RHS uses (foundational `Classical.choice`
//! closure); everything else is pure λ (no axiom content), so every consumer
//! stays `KernelVerified` to the three foundationals.

use clean_kernel::expr::FVarId;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Expr};

use super::super::super::isabelle_pure::IsaType;
use super::super::{fun_split, obj_level, Ctx, TranslateError};
use super::sets::{ball_encoding, image_encoding};
use super::{conj_def_const, hol_if_def_name};

/// The kernel declaration name of the clean polymorphic `Definition` registered
/// for a `Fun.*` combinator constant, or `None` for any other name.
pub(crate) fn fun_def_const_name(name: &str) -> Option<&'static str> {
    match name {
        "Fun.fcomp" => Some("isabelle.def.Fun.fcomp"),
        "Fun.inj_on" => Some("isabelle.def.Fun.inj_on"),
        "Fun.bij_betw" => Some("isabelle.def.Fun.bij_betw"),
        "Fun.fun_upd" => Some("isabelle.def.Fun.fun_upd"),
        "Fun.monotone_on" => Some("isabelle.def.Fun.monotone_on"),
        _ => None,
    }
}

/// `Fun.fcomp : ('a⇒'b) ⇒ ('b⇒'c) ⇒ 'a ⇒ 'c := λf g x. g (f x)` — forward
/// composition (`fcomp_def_raw`: `f ∘> g = (λx. g (f x))`). Three leading `Type`
/// binders α, β, γ in the constant's own type-variable order.
fn build_fcomp() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a201); // α
    let fb = FVarId::new(0x1_a202); // β
    let fg = FVarId::new(0x1_a203); // γ
    let ff = FVarId::new(0x1_a204); // f : α → β
    let fgf = FVarId::new(0x1_a205); // g : β → γ
    let fx = FVarId::new(0x1_a206); // x : α
    let alpha = || Expr::fvar(fa);
    let beta = || Expr::fvar(fb);
    let gamma = || Expr::fvar(fg);
    let f_ty = || Expr::arrow(alpha(), beta());
    let g_ty = || Expr::arrow(beta(), gamma());

    // body: g (f x) : γ.
    let body = Expr::app(Expr::fvar(fgf), Expr::app(Expr::fvar(ff), Expr::fvar(fx)));
    // value: λ(α β γ:Type)(f:α→β)(g:β→γ)(x:α). g (f x) — abstract innermost-first.
    let v = body.abstract_fvar(fx);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fgf);
    let v = Expr::lam(BinderInfo::Default, g_ty(), v);
    let v = v.abstract_fvar(ff);
    let v = Expr::lam(BinderInfo::Default, f_ty(), v);
    let v = v.abstract_fvar(fg);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α β γ:Type)(f:α→β)(g:β→γ)(x:α). γ.
    let t = gamma().abstract_fvar(fx);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fgf);
    let t = Expr::pi(BinderInfo::Default, g_ty(), t);
    let t = t.abstract_fvar(ff);
    let t = Expr::pi(BinderInfo::Default, f_ty(), t);
    let t = t.abstract_fvar(fg);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fb);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `Fun.inj_on : ('a⇒'b) ⇒ 'a set ⇒ bool
///   := λf A. Ball A (λx. Ball A (λy. f x = f y → x = y))`
/// (`inj_on_def_raw`) — the body is the `Set.Ball` bounded-∀ ([`ball_encoding`])
/// applied exactly as the `_def` RHS embeds it, so the two sides are βδ-equal.
fn build_inj_on() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a301); // α
    let fb = FVarId::new(0x1_a302); // β
    let ff = FVarId::new(0x1_a303); // f : α → β
    let fset = FVarId::new(0x1_a304); // A : α → Prop
    let fx = FVarId::new(0x1_a305); // x : α
    let fy = FVarId::new(0x1_a306); // y : α
    let alpha = || Expr::fvar(fa);
    let beta = || Expr::fvar(fb);
    let f = || Expr::fvar(ff);
    let a = || Expr::fvar(fset);
    let fn_ty = || Expr::arrow(alpha(), beta());
    let set_ty = || Expr::arrow(alpha(), Expr::prop());

    // inner: λ(y:α)-position body  f x = f y → x = y
    let eq_fxy = Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [
            beta(),
            Expr::app(f(), Expr::fvar(fx)),
            Expr::app(f(), Expr::fvar(fy)),
        ],
    );
    let eq_xy = Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [alpha(), Expr::fvar(fx), Expr::fvar(fy)],
    );
    let imp = Expr::arrow(eq_fxy, eq_xy);
    let lam_y = Expr::lam(BinderInfo::Default, alpha(), imp.abstract_fvar(fy));
    // Ball A (λy. …) — the SAME `ball_encoding` application the RHS embeds to.
    let inner_ball = Expr::apps(ball_encoding(&alpha()), [a(), lam_y]);
    let lam_x = Expr::lam(BinderInfo::Default, alpha(), inner_ball.abstract_fvar(fx));
    let body = Expr::apps(ball_encoding(&alpha()), [a(), lam_x]);

    // value: λ(α β:Type)(f:α→β)(A:α→Prop). body.
    let v = body.abstract_fvar(fset);
    let v = Expr::lam(BinderInfo::Default, set_ty(), v);
    let v = v.abstract_fvar(ff);
    let v = Expr::lam(BinderInfo::Default, fn_ty(), v);
    let v = v.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α β:Type)(f:α→β)(A:α→Prop). Prop.
    let t = Expr::prop().abstract_fvar(fset);
    let t = Expr::pi(BinderInfo::Default, set_ty(), t);
    let t = t.abstract_fvar(ff);
    let t = Expr::pi(BinderInfo::Default, fn_ty(), t);
    let t = t.abstract_fvar(fb);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `Fun.bij_betw : ('a⇒'b) ⇒ 'a set ⇒ 'b set ⇒ bool
///   := λf A B. inj_on f A ∧ (image f A = B)`
/// (`bij_betw_def_raw`) — the `inj_on` conjunct is the registered
/// `isabelle.def.Fun.inj_on` def-const applied (matching how the `_def` RHS's own
/// `inj_on ?f ?A` embeds), the image the shared [`image_encoding`], the set
/// equality the object-level `@Eq (β→Prop)`, the `∧` the `HOL.conj` def-const.
fn build_bij_betw() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a401); // α
    let fb = FVarId::new(0x1_a402); // β
    let ff = FVarId::new(0x1_a403); // f : α → β
    let fseta = FVarId::new(0x1_a404); // A : α → Prop
    let fsetb = FVarId::new(0x1_a405); // B : β → Prop
    let alpha = || Expr::fvar(fa);
    let beta = || Expr::fvar(fb);
    let fn_ty = || Expr::arrow(alpha(), beta());
    let seta_ty = || Expr::arrow(alpha(), Expr::prop());
    let setb_ty = || Expr::arrow(beta(), Expr::prop());

    // inj_on f A — the registered def-const (same head the RHS occurrence uses).
    let inj = Expr::apps(
        Expr::const_str("isabelle.def.Fun.inj_on"),
        [alpha(), beta(), Expr::fvar(ff), Expr::fvar(fseta)],
    );
    // image f A = B  at the set type β→Prop.
    let img = Expr::apps(
        image_encoding(&alpha(), &beta()),
        [Expr::fvar(ff), Expr::fvar(fseta)],
    );
    let eq_img = Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [setb_ty(), img, Expr::fvar(fsetb)],
    );
    let body = Expr::apps(conj_def_const(), [inj, eq_img]);

    // value: λ(α β:Type)(f:α→β)(A:α→Prop)(B:β→Prop). body.
    let v = body.abstract_fvar(fsetb);
    let v = Expr::lam(BinderInfo::Default, setb_ty(), v);
    let v = v.abstract_fvar(fseta);
    let v = Expr::lam(BinderInfo::Default, seta_ty(), v);
    let v = v.abstract_fvar(ff);
    let v = Expr::lam(BinderInfo::Default, fn_ty(), v);
    let v = v.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α β:Type)(f:α→β)(A:α→Prop)(B:β→Prop). Prop.
    let t = Expr::prop().abstract_fvar(fsetb);
    let t = Expr::pi(BinderInfo::Default, setb_ty(), t);
    let t = t.abstract_fvar(fseta);
    let t = Expr::pi(BinderInfo::Default, seta_ty(), t);
    let t = t.abstract_fvar(ff);
    let t = Expr::pi(BinderInfo::Default, fn_ty(), t);
    let t = t.abstract_fvar(fb);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `Fun.fun_upd : ('a⇒'b) ⇒ 'a ⇒ 'b ⇒ 'a ⇒ 'b
///   := λf a b x. if x = a then b else f x`
/// (`fun_upd_def_raw`) — the `if` is the SAME `isabelle.def.HOL.If` def-const
/// (at the object level) the `_def` RHS embeds to, the equality the object-level
/// `@Eq α`.
fn build_fun_upd() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a501); // α
    let fb = FVarId::new(0x1_a502); // β
    let ff = FVarId::new(0x1_a503); // f : α → β
    let fpt = FVarId::new(0x1_a504); // a : α
    let fvl = FVarId::new(0x1_a505); // b : β
    let fx = FVarId::new(0x1_a506); // x : α
    let alpha = || Expr::fvar(fa);
    let beta = || Expr::fvar(fb);
    let fn_ty = || Expr::arrow(alpha(), beta());

    // if (x = a) then b else (f x)  —  @isabelle.def.HOL.If.{1} β cond b (f x).
    let cond = Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [alpha(), Expr::fvar(fx), Expr::fvar(fpt)],
    );
    let if_head = Expr::app(
        Expr::const_str_levels(hol_if_def_name(), vec![obj_level()]),
        beta(),
    );
    let body = Expr::apps(
        if_head,
        [
            cond,
            Expr::fvar(fvl),
            Expr::app(Expr::fvar(ff), Expr::fvar(fx)),
        ],
    );

    // value: λ(α β:Type)(f:α→β)(a:α)(b:β)(x:α). body.
    let v = body.abstract_fvar(fx);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(fvl);
    let v = Expr::lam(BinderInfo::Default, beta(), v);
    let v = v.abstract_fvar(fpt);
    let v = Expr::lam(BinderInfo::Default, alpha(), v);
    let v = v.abstract_fvar(ff);
    let v = Expr::lam(BinderInfo::Default, fn_ty(), v);
    let v = v.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α β:Type)(f:α→β)(a:α)(b:β)(x:α). β.
    let t = beta().abstract_fvar(fx);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(fvl);
    let t = Expr::pi(BinderInfo::Default, beta(), t);
    let t = t.abstract_fvar(fpt);
    let t = Expr::pi(BinderInfo::Default, alpha(), t);
    let t = t.abstract_fvar(ff);
    let t = Expr::pi(BinderInfo::Default, fn_ty(), t);
    let t = t.abstract_fvar(fb);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// `Fun.monotone_on : 'a set ⇒ ('a⇒'a⇒bool) ⇒ ('b⇒'b⇒bool) ⇒ ('a⇒'b) ⇒ bool
///   := λA le_a le_b f. Ball A (λx. Ball A (λy. le_a x y → le_b (f x) (f y)))`
/// (`monotone_on_def_raw`) — the body is the `Set.Ball` bounded-∀
/// ([`ball_encoding`]) applied exactly as the `_def` RHS embeds it.
fn build_monotone_on() -> (Expr, Expr) {
    let fa = FVarId::new(0x1_a601); // α
    let fb = FVarId::new(0x1_a602); // β
    let fset = FVarId::new(0x1_a603); // A : α → Prop
    let flea = FVarId::new(0x1_a604); // le_a : α → α → Prop
    let fleb = FVarId::new(0x1_a605); // le_b : β → β → Prop
    let ff = FVarId::new(0x1_a606); // f : α → β
    let fx = FVarId::new(0x1_a607); // x : α
    let fy = FVarId::new(0x1_a608); // y : α
    let alpha = || Expr::fvar(fa);
    let beta = || Expr::fvar(fb);
    let a = || Expr::fvar(fset);
    let f = || Expr::fvar(ff);
    let set_ty = || Expr::arrow(alpha(), Expr::prop());
    let lea_ty = || Expr::arrow(alpha(), Expr::arrow(alpha(), Expr::prop()));
    let leb_ty = || Expr::arrow(beta(), Expr::arrow(beta(), Expr::prop()));
    let fn_ty = || Expr::arrow(alpha(), beta());

    // le_a x y → le_b (f x) (f y)
    let lea_xy = Expr::apps(Expr::fvar(flea), [Expr::fvar(fx), Expr::fvar(fy)]);
    let leb_fxy = Expr::apps(
        Expr::fvar(fleb),
        [
            Expr::app(f(), Expr::fvar(fx)),
            Expr::app(f(), Expr::fvar(fy)),
        ],
    );
    let imp = Expr::arrow(lea_xy, leb_fxy);
    let lam_y = Expr::lam(BinderInfo::Default, alpha(), imp.abstract_fvar(fy));
    let inner_ball = Expr::apps(ball_encoding(&alpha()), [a(), lam_y]);
    let lam_x = Expr::lam(BinderInfo::Default, alpha(), inner_ball.abstract_fvar(fx));
    let body = Expr::apps(ball_encoding(&alpha()), [a(), lam_x]);

    // value: λ(α β:Type)(A:α→Prop)(le_a)(le_b)(f:α→β). body.
    let v = body.abstract_fvar(ff);
    let v = Expr::lam(BinderInfo::Default, fn_ty(), v);
    let v = v.abstract_fvar(fleb);
    let v = Expr::lam(BinderInfo::Default, leb_ty(), v);
    let v = v.abstract_fvar(flea);
    let v = Expr::lam(BinderInfo::Default, lea_ty(), v);
    let v = v.abstract_fvar(fset);
    let v = Expr::lam(BinderInfo::Default, set_ty(), v);
    let v = v.abstract_fvar(fb);
    let v = Expr::lam(BinderInfo::Default, Expr::type_(), v);
    let v = v.abstract_fvar(fa);
    let value = Expr::lam(BinderInfo::Default, Expr::type_(), v);

    // type: Π(α β:Type)(A:α→Prop)(le_a)(le_b)(f:α→β). Prop.
    let t = Expr::prop().abstract_fvar(ff);
    let t = Expr::pi(BinderInfo::Default, fn_ty(), t);
    let t = t.abstract_fvar(fleb);
    let t = Expr::pi(BinderInfo::Default, leb_ty(), t);
    let t = t.abstract_fvar(flea);
    let t = Expr::pi(BinderInfo::Default, lea_ty(), t);
    let t = t.abstract_fvar(fset);
    let t = Expr::pi(BinderInfo::Default, set_ty(), t);
    let t = t.abstract_fvar(fb);
    let t = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    let t = t.abstract_fvar(fa);
    let type_ = Expr::pi(BinderInfo::Default, Expr::type_(), t);
    (value, type_)
}

/// The `Fun.*` combinator constants as clean [`Declaration::Definition`]s, in
/// dependency order (`inj_on` before `bij_betw`, whose body references it).
/// Registered into the verifier's accumulating environment up front (like
/// [`super::connective_definition_decls`]) so each constant's occurrences share
/// one defeq-unfolding head and its `…_def`/`…_def_raw` axiom verifies
/// reflexively. Registered AFTER the connective/`HOL.If` def-consts (their
/// bodies' dependencies), so the δ-unfolding chain closes. Non-fatal on
/// registration failure: the constant's nodes simply stay unmapped, exactly as
/// before — never mis-registered.
#[must_use]
pub(crate) fn fun_combinator_definition_decls() -> Vec<Declaration> {
    let entries: [(&str, (Expr, Expr)); 5] = [
        ("Fun.fcomp", build_fcomp()),
        ("Fun.inj_on", build_inj_on()),
        ("Fun.bij_betw", build_bij_betw()),
        ("Fun.fun_upd", build_fun_upd()),
        ("Fun.monotone_on", build_monotone_on()),
    ];
    entries
        .into_iter()
        .filter_map(|(name, (value, type_))| {
            fun_def_const_name(name).map(|def| Declaration::Definition {
                name: Name::from_string(def),
                level_params: Vec::new(),
                type_,
                value,
                is_reducible: true,
            })
        })
        .collect()
}

impl Ctx {
    /// Embed an occurrence of a `Fun.*` combinator constant
    /// (`fcomp`/`inj_on`/`bij_betw`/`fun_upd`/`monotone_on`) to its registered
    /// polymorphic def-const ([`fun_def_const_name`]) applied to the use-site's
    /// solved object types, so the constant's `…_def`/`…_def_raw` axiom verifies
    /// reflexively (`C args` δβ-reduces to the embedded body) and every occurrence
    /// shares one defeq-unfolding head. `use_ty` is the constant's instantiated
    /// HOL type; the object type parameters are read from its arrow structure.
    /// Returns `None` when `use_ty` is not the expected shape (the caller then
    /// falls back to the opaque `const:` param; the kernel re-checks either way).
    pub(crate) fn embed_fun_combinator(
        &mut self,
        n: &str,
        use_ty: &IsaType,
    ) -> Result<Option<Expr>, TranslateError> {
        let Some(def) = fun_def_const_name(n) else {
            return Ok(None);
        };
        // The object type arguments, in the def-const's leading-binder order.
        let type_args: Vec<&IsaType> = match n {
            // `(α⇒β) ⇒ (β⇒γ) ⇒ α ⇒ γ` — α, β off the first arrow; γ off the
            // second operand's codomain.
            "Fun.fcomp" => {
                let Some((f_ty, rest)) = fun_split(use_ty) else {
                    return Ok(None);
                };
                let Some((alpha_ty, beta_ty)) = fun_split(f_ty) else {
                    return Ok(None);
                };
                let Some((g_ty, _)) = fun_split(rest) else {
                    return Ok(None);
                };
                let Some((_b2, gamma_ty)) = fun_split(g_ty) else {
                    return Ok(None);
                };
                vec![alpha_ty, beta_ty, gamma_ty]
            }
            // `(α⇒β) ⇒ …` — α, β off the first (function) operand.
            "Fun.inj_on" | "Fun.bij_betw" | "Fun.fun_upd" => {
                let Some((f_ty, _)) = fun_split(use_ty) else {
                    return Ok(None);
                };
                let Some((alpha_ty, beta_ty)) = fun_split(f_ty) else {
                    return Ok(None);
                };
                vec![alpha_ty, beta_ty]
            }
            // `'a set ⇒ ('a⇒'a⇒bool) ⇒ ('b⇒'b⇒bool) ⇒ ('a⇒'b) ⇒ bool` — α off
            // the second operand's (order-relation) domain, β off the third's.
            "Fun.monotone_on" => {
                let Some((_set_ty, rest1)) = fun_split(use_ty) else {
                    return Ok(None);
                };
                let Some((lea_ty, rest2)) = fun_split(rest1) else {
                    return Ok(None);
                };
                let Some((alpha_ty, _)) = fun_split(lea_ty) else {
                    return Ok(None);
                };
                let Some((leb_ty, _)) = fun_split(rest2) else {
                    return Ok(None);
                };
                let Some((beta_ty, _)) = fun_split(leb_ty) else {
                    return Ok(None);
                };
                vec![alpha_ty, beta_ty]
            }
            _ => return Ok(None),
        };
        let mut e = Expr::const_str(def);
        for ty in type_args {
            let te = self.embed_type(ty)?;
            e = Expr::app(e, te);
        }
        Ok(Some(e))
    }
}

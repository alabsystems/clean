// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HOL's `If_def` — the characterisation of if-then-else through definite
//! description:
//!
//! ```text
//! If P x y ≡ THE z. (P = True ⟶ z = x) ∧ (P = False ⟶ z = y)
//! ```
//!
//! Under the embedding the two sides are genuinely **different** classical
//! programs: the LHS `isabelle.def.HOL.If` is `ite` over a classical
//! `Decidable P` instance, the RHS `isabelle.def.HOL.The` is the guard-subtype
//! epsilon (`Classical.choice`). They are *propositionally* (not definitionally)
//! equal, so no reflexive arm can land this axiom — this module proves the real
//! equation by excluded middle:
//!
//! - **case `h : P`**: `ite P dec x y = x` by `Decidable.casesOn` on the
//!   (opaque) classical instance — the `isTrue` arm ι-reduces `ite` to `x`, the
//!   `isFalse` arm is absurd (`hn h`); and `THE z. … = x` by the epsilon's
//!   defining property `(∃z. pred z) → pred (THE …)` with witness `x` (the first
//!   conjunct applied to `P = True`, proved by `propext`). Chain with
//!   `Eq.trans`/`Eq.symm`.
//! - **case `hn : ¬P`**: symmetric with `y` and the second conjunct
//!   (`P = False` by `propext`).
//!
//! Every ingredient is `Classical.em`/`Classical.choice`/`propext`-based
//! (foundational closure), and the kernel re-checks the whole term against the
//! embedded statement — a wrong bridge is rejected, never miscounted. `If_def`
//! is the sole characterising axiom of `HOL.If`, so landing it unblocks the
//! `if_True`/`if_False`/`if_cong` family that references its `…_def_raw` leaf.

use clean_kernel::expr::{ExprKind, FVarId};
use clean_kernel::level::Level;
use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::{IsaProvenTheorem, IsaTerm};
use super::super::*;

/// If `tm` is `HOL.If $ P $ x $ y`, return `(P, x, y)`.
fn hol_if_parts(tm: &IsaTerm) -> Option<(&IsaTerm, &IsaTerm, &IsaTerm)> {
    let IsaTerm::App { f, a: y } = tm else {
        return None;
    };
    let IsaTerm::App { f: fx, a: x } = f.as_ref() else {
        return None;
    };
    let IsaTerm::App { f: fc, a: p } = fx.as_ref() else {
        return None;
    };
    let IsaTerm::Const { n, .. } = fc.as_ref() else {
        return None;
    };
    if n != "HOL.If" {
        return None;
    }
    Some((p, x, y))
}

/// The classical `Decidable c` instance the `isabelle.def.HOL.If` definition
/// value carries, rebuilt at a concrete condition `c` — the EXACT term the
/// def-const's body δβ-substitutes, so `ite α c (dec_inst c) x y` is
/// definitionally the unfolded `@isabelle.def.HOL.If.{1} α c x y`. Mirrors
/// [`super::super::build_hol_if_value_and_type`] verbatim.
fn classical_dec_inst(c: &Expr) -> Expr {
    let l1 = Level::succ(Level::zero());
    let dec = |c: Expr| Expr::app(Expr::const_str("Decidable"), c);
    let not_c = Expr::arrow(c.clone(), Expr::const_str("False"));
    let or_c = Expr::apps(Expr::const_str("Or"), [c.clone(), not_c.clone()]);
    let fh = FVarId::new(0x1_b001);
    // motive: λ_:Or c (¬c). Nonempty (Decidable c)
    let motive = Expr::lam(
        BinderInfo::Default,
        or_c,
        Expr::app(
            Expr::const_str_levels("Nonempty", vec![l1.clone()]),
            dec(c.clone()),
        ),
    );
    let pos_body = Expr::apps(
        Expr::const_str_levels("Nonempty.intro", vec![l1.clone()]),
        [
            dec(c.clone()),
            Expr::apps(
                Expr::const_str("Decidable.isTrue"),
                [c.clone(), Expr::fvar(fh)],
            ),
        ],
    );
    let pos = Expr::lam(BinderInfo::Default, c.clone(), pos_body.abstract_fvar(fh));
    let neg_body = Expr::apps(
        Expr::const_str_levels("Nonempty.intro", vec![l1.clone()]),
        [
            dec(c.clone()),
            Expr::apps(
                Expr::const_str("Decidable.isFalse"),
                [c.clone(), Expr::fvar(fh)],
            ),
        ],
    );
    let neg = Expr::lam(
        BinderInfo::Default,
        not_c.clone(),
        neg_body.abstract_fvar(fh),
    );
    let em = Expr::app(Expr::const_str("Classical.em"), c.clone());
    let nonempty_dec = Expr::apps(
        Expr::const_str("Or.rec"),
        [c.clone(), not_c, motive, pos, neg, em],
    );
    Expr::apps(
        Expr::const_str_levels("Classical.choice", vec![l1]),
        [dec(c.clone()), nonempty_dec],
    )
}

/// `@ite.{1} α c d x y` — the prelude if-then-else applied at the object level.
fn ite_app(alpha: &Expr, c: &Expr, d: &Expr, x: &Expr, y: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("ite", vec![obj_level()]),
        [alpha.clone(), c.clone(), d.clone(), x.clone(), y.clone()],
    )
}

/// `@Eq.{1} α a b`.
fn eq_at(alpha: &Expr, a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![obj_level()]),
        [alpha.clone(), a.clone(), b.clone()],
    )
}

/// Prove `@Eq α (@ite α P (dec_inst P) x y) BRANCH` (`BRANCH` = `x` under
/// `h : P`, `y` under `hn : P → False`) by `Decidable.casesOn` on the classical
/// instance: one arm ι-reduces `ite` to the branch (`Eq.refl`), the other is
/// absurd. `evidence` is the case hypothesis (`h`/`hn`), `pos` selects which.
fn ite_eq_branch(alpha: &Expr, p: &Expr, x: &Expr, y: &Expr, evidence: &Expr, pos: bool) -> Expr {
    let branch = if pos { x } else { y };
    let not_p = Expr::arrow(p.clone(), Expr::const_str("False"));
    // motive: λ(d : Decidable P). @Eq α (ite α P d x y) BRANCH
    let fd = FVarId::new(0x1_b101);
    let d = Expr::fvar(fd);
    let motive_body = eq_at(alpha, &ite_app(alpha, p, &d, x, y), branch);
    let dec_p = Expr::app(Expr::const_str("Decidable"), p.clone());
    let motive = Expr::lam(BinderInfo::Default, dec_p, motive_body.abstract_fvar(fd));
    // isFalse arm: λ(hn2 : ¬P). …
    let fhn = FVarId::new(0x1_b102);
    let false_arm = {
        let body = if pos {
            // absurd: hn2 h : False; target = motive (isFalse hn2).
            let is_false = Expr::apps(
                Expr::const_str("Decidable.isFalse"),
                [p.clone(), Expr::fvar(fhn)],
            );
            let target = eq_at(alpha, &ite_app(alpha, p, &is_false, x, y), branch);
            Expr::apps(
                Expr::const_str_levels("False.elim", vec![Level::zero()]),
                [target, Expr::app(Expr::fvar(fhn), evidence.clone())],
            )
        } else {
            // ite (isFalse hn2) ι-reduces to y = BRANCH: Eq.refl.
            Expr::apps(
                Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                [alpha.clone(), y.clone()],
            )
        };
        Expr::lam(BinderInfo::Default, not_p, body.abstract_fvar(fhn))
    };
    // isTrue arm: λ(ht : P). …
    let fht = FVarId::new(0x1_b103);
    let true_arm = {
        let body = if pos {
            // ite (isTrue ht) ι-reduces to x = BRANCH: Eq.refl.
            Expr::apps(
                Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                [alpha.clone(), x.clone()],
            )
        } else {
            // absurd: hn ht : False; target = motive (isTrue ht).
            let is_true = Expr::apps(
                Expr::const_str("Decidable.isTrue"),
                [p.clone(), Expr::fvar(fht)],
            );
            let target = eq_at(alpha, &ite_app(alpha, p, &is_true, x, y), branch);
            Expr::apps(
                Expr::const_str_levels("False.elim", vec![Level::zero()]),
                [target, Expr::app(evidence.clone(), Expr::fvar(fht))],
            )
        };
        Expr::lam(BinderInfo::Default, p.clone(), body.abstract_fvar(fht))
    };
    // Decidable.casesOn.{0} P motive MAJOR falseArm trueArm  (Lean-faithful
    // order: motive, major, then minors — see `logic_ite.rs`).
    Expr::apps(
        Expr::const_str_levels("Decidable.casesOn", vec![Level::zero()]),
        [
            p.clone(),
            motive,
            classical_dec_inst(p),
            false_arm,
            true_arm,
        ],
    )
}

/// The conjunct pair `(A, B)` of `pred z₀ = conj A B` — `pred`'s lambda body
/// instantiated at `z₀` and split at the `isabelle.def.HOL.conj` application.
fn pred_conjuncts_at(pred: &Expr, z0: &Expr) -> Option<(Expr, Expr)> {
    let ExprKind::Lam(_, _, body) = pred.kind() else {
        return None;
    };
    let at = body.instantiate(z0);
    // conj A B  =  App(App(Const conj, A), B).
    let ExprKind::App(f, b) = at.kind() else {
        return None;
    };
    let ExprKind::App(cf, a) = f.kind() else {
        return None;
    };
    let ExprKind::Const(n, _) = cf.kind() else {
        return None;
    };
    if n.to_string() != "isabelle.def.HOL.conj" {
        return None;
    }
    Some(((**a).clone(), (**b).clone()))
}

/// The impredicative-`conj` introduction `λ(C:Prop)(k:A→B→C). k ha hb` — an
/// inhabitant of `conj A B`'s encoding `∀C. (A→B→C)→C` (the kernel δ-unfolds
/// the def-const when checking it against `pred z₀`).
fn conj_intro(a: &Expr, b: &Expr, ha: Expr, hb: Expr) -> Expr {
    let fc = FVarId::new(0x1_b201);
    let fk = FVarId::new(0x1_b202);
    let c = Expr::fvar(fc);
    let k_ty = Expr::arrow(a.clone(), Expr::arrow(b.clone(), c.clone()));
    let body = Expr::apps(Expr::fvar(fk), [ha, hb]);
    let lam_k = Expr::lam(BinderInfo::Default, k_ty, body.abstract_fvar(fk));
    Expr::lam(BinderInfo::Default, Expr::prop(), lam_k.abstract_fvar(fc))
}

/// The impredicative-`conj` elimination `pf C (λ(h1:A)(h2:B). select)` — apply
/// the encoded conjunction `pf : conj A B` at target `C` with the two-hypothesis
/// continuation `select(h1, h2)`.
fn conj_elim(
    a: &Expr,
    b: &Expr,
    pf: &Expr,
    c: &Expr,
    select: impl FnOnce(Expr, Expr) -> Expr,
) -> Expr {
    let fh1 = FVarId::new(0x1_b203);
    let fh2 = FVarId::new(0x1_b204);
    let body = select(Expr::fvar(fh1), Expr::fvar(fh2));
    let lam2 = Expr::lam(BinderInfo::Default, b.clone(), body.abstract_fvar(fh2));
    let lam1 = Expr::lam(BinderInfo::Default, a.clone(), lam2.abstract_fvar(fh1));
    Expr::apps(pf.clone(), [c.clone(), lam1])
}

impl Ctx {
    /// Statement-level proof of HOL's `If_def`
    /// (`If P x y ≡ THE z. (P=True ⟶ z=x) ∧ (P=False ⟶ z=y)`) — both the
    /// **applied** form (the named `If_def`) and the **point-free** raw form
    /// (`If ≡ λP x y. THE z. …`, the anonymous `If_def_raw` consumer; proved by
    /// wrapping the pointwise core in three `funext`s) — attempted BEFORE the
    /// recorded proof (whose `If_def_raw` PAxm leaf is unmapped). Returns the
    /// `(stored_type, proof)` pair, or `None` if `thm` is not `If_def`-shaped.
    /// Gated on `instance_unfold` (the pass where `HOL.If`/`HOL.The` route to
    /// their def-consts). See the module doc for the proof; the kernel re-checks
    /// it against the REAL embedded equation (two genuinely different classical
    /// programs — never a `B = B` tautology), so a wrong bridge is rejected.
    pub(crate) fn prove_hol_if_def(
        &mut self,
        thm: &IsaProvenTheorem,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<(Expr, Expr)>, TranslateError> {
        if !self.instance_unfold {
            return Ok(None);
        }
        let concl = strip_leading_imps(&thm.prop);
        let (lhs_tm, rhs_tm) = match pure_eq_parts(concl) {
            Some(p) => p,
            None => return Ok(None),
        };
        // Applied form: LHS `HOL.If P x y`, RHS `HOL.The (λz. …)`. Point-free
        // form: LHS the BARE `HOL.If`, RHS `λP x y. HOL.The (λz. …)`.
        let applied = hol_if_parts(lhs_tm).is_some();
        let pointfree = matches!(lhs_tm, IsaTerm::Const { n, .. } if n == "HOL.If");
        if !applied && !pointfree {
            return Ok(None);
        }
        if applied {
            let IsaTerm::App { f: the_f, .. } = rhs_tm else {
                return Ok(None);
            };
            if !is_const(the_f, "HOL.The") {
                return Ok(None);
            }
        }
        // Embed both sides through the ordinary dispatch: `HOL.If` routes to
        // `@isabelle.def.HOL.If.{1} α [P x y]`, the `HOL.The` occurrence to
        // `@isabelle.def.HOL.The α hne pred` (shared `Nonempty α` param).
        let lhs_e = self.embed_term(lhs_tm, binders)?;
        let rhs_e = self.embed_term(rhs_tm, binders)?;
        if applied {
            let (if_args, if_head) = app_spine(&lhs_e);
            if !is_named(&if_head, hol_if_def_name()) || if_args.len() != 4 {
                return Ok(None);
            }
            let (alpha, p, x, y) = (&if_args[0], &if_args[1], &if_args[2], &if_args[3]);
            let Some(core) = hol_if_the_core(alpha, p, x, y, &lhs_e, &rhs_e) else {
                return Ok(None);
            };
            let goal = eq_at(alpha, &lhs_e, &rhs_e);
            return Ok(Some(discharge_sort_premises(thm, goal, core)));
        }
        // ── point-free form ──
        // lhs_e = `@isabelle.def.HOL.If.{1} α` (the bare constant routed at its
        // use type `bool ⇒ α ⇒ α ⇒ α`); rhs_e = `λ(P:Prop)(x:α)(y:α). THE …`.
        let (if_args, if_head) = app_spine(&lhs_e);
        if !is_named(&if_head, hol_if_def_name()) || if_args.len() != 1 {
            return Ok(None);
        }
        let alpha = &if_args[0];
        // Open the three RHS lambda binders at fresh fvars.
        let fp = FVarId::new(0x1_b501);
        let fx = FVarId::new(0x1_b502);
        let fy = FVarId::new(0x1_b503);
        let (p, x, y) = (Expr::fvar(fp), Expr::fvar(fx), Expr::fvar(fy));
        let ExprKind::Lam(_, _, b1) = rhs_e.kind() else {
            return Ok(None);
        };
        let g2 = b1.instantiate(&p); // λ(x:α)(y:α). THE …   [at P]
        let ExprKind::Lam(_, _, b2) = g2.kind() else {
            return Ok(None);
        };
        let g3 = b2.instantiate(&x); // λ(y:α). THE …   [at P, x]
        let ExprKind::Lam(_, _, b3) = g3.kind() else {
            return Ok(None);
        };
        let the_at = b3.instantiate(&y); // THE …   [at P, x, y]
        let lhs_point = Expr::apps(lhs_e.clone(), [p.clone(), x.clone(), y.clone()]);
        let Some(core) = hol_if_the_core(alpha, &p, &x, &y, &lhs_point, &the_at) else {
            return Ok(None);
        };
        // Wrap the pointwise core in three `funext`s (innermost `y` first). All
        // domains/codomains live at the object level, so every `funext` is
        // `.{1,1}`; each family is the constant `λ_. <residual fn type>`.
        let fn_a = |cod: &Expr| Expr::arrow(alpha.clone(), cod.clone());
        // y-level: f = `If α P x`, g = `λy. THE …`.
        let pw3 = Expr::lam(BinderInfo::Default, alpha.clone(), core.abstract_fvar(fy));
        let fam3 = Expr::lam(BinderInfo::Default, alpha.clone(), alpha.clone());
        let f3 = Expr::apps(lhs_e.clone(), [p.clone(), x.clone()]);
        let eq3 = Expr::apps(
            Expr::const_str_levels("funext", vec![obj_level(), obj_level()]),
            [alpha.clone(), fam3, f3, g3.clone(), pw3],
        );
        // x-level: f = `If α P`, g = `λx y. THE …`.
        let pw2 = Expr::lam(BinderInfo::Default, alpha.clone(), eq3.abstract_fvar(fx));
        let fam2 = Expr::lam(BinderInfo::Default, alpha.clone(), fn_a(alpha));
        let f2 = Expr::app(lhs_e.clone(), p.clone());
        let eq2 = Expr::apps(
            Expr::const_str_levels("funext", vec![obj_level(), obj_level()]),
            [alpha.clone(), fam2, f2, g2.clone(), pw2],
        );
        // P-level: f = `If α`, g = the full RHS lambda.
        let pw1 = Expr::lam(BinderInfo::Default, Expr::prop(), eq2.abstract_fvar(fp));
        let fam1 = Expr::lam(BinderInfo::Default, Expr::prop(), fn_a(&fn_a(alpha)));
        let eq1 = Expr::apps(
            Expr::const_str_levels("funext", vec![obj_level(), obj_level()]),
            [Expr::prop(), fam1, lhs_e.clone(), rhs_e.clone(), pw1],
        );
        let goal = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [Expr::arrow(Expr::prop(), fn_a(&fn_a(alpha))), lhs_e, rhs_e],
        );
        Ok(Some(discharge_sort_premises(thm, goal, eq1)))
    }
}

/// Wrap `(goal, core)` with one vacuous `True →` / `fun (_:True) =>` per
/// leading (erased sort-constraint) premise of `thm`, in lockstep.
fn discharge_sort_premises(thm: &IsaProvenTheorem, goal: Expr, core: Expr) -> (Expr, Expr) {
    let n_premises = leading_premises(&thm.prop).len();
    let mut proof = core;
    let mut stored = goal;
    for _ in 0..n_premises {
        proof = Expr::lam(BinderInfo::Default, Expr::const_str("True"), proof);
        stored = Expr::arrow(Expr::const_str("True"), stored);
    }
    (stored, proof)
}

/// Whether `e` is the `Const` named `name` (any levels).
fn is_named(e: &Expr, name: &str) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

/// The pointwise `If_def` core: a kernel proof of
/// `@Eq α (If α P x y) (THE z. (P=True ⟶ z=x) ∧ (P=False ⟶ z=y))` at fixed
/// embedded `α`/`P`/`x`/`y`. `lhs_point` is the saturated
/// `@isabelle.def.HOL.If.{1} α P x y`; `the_at` the saturated
/// `@isabelle.def.HOL.The α hne pred`. Returns `None` when `the_at` does not
/// decompose to the expected epsilon/conjunction shape (the caller falls back;
/// the kernel re-checks any produced term, so a wrong build only rejects).
#[allow(clippy::many_single_char_names)]
fn hol_if_the_core(
    alpha: &Expr,
    p: &Expr,
    x: &Expr,
    y: &Expr,
    lhs_point: &Expr,
    the_at: &Expr,
) -> Option<Expr> {
    {
        let (the_args, the_head) = app_spine(the_at);
        if !is_named(&the_head, hol_the_def_name()) || the_args.len() != 3 {
            return None;
        }
        let (hne, pred) = (&the_args[1], &the_args[2]);

        // The conjunct pairs of `pred` at the three points of interest. Each `A`
        // is `(P = True) → (z = x)`, each `B` is `(P = False) → (z = y)`; the
        // `P = True`/`P = False` hypothesis types are read off `A`/`B` directly.
        let (a_the, b_the) = pred_conjuncts_at(pred, the_at)?;
        let (a_x, b_x) = pred_conjuncts_at(pred, x)?;
        let (a_y, b_y) = pred_conjuncts_at(pred, y)?;
        // A = Pi(_ : P=True). z=x  — non-dependent arrow; split hypothesis types.
        let split_arrow_e = |e: &Expr| -> Option<(Expr, Expr)> {
            match e.kind() {
                ExprKind::Pi(_, dom, cod) => Some(((**dom).clone(), (**cod).clone())),
                _ => None,
            }
        };
        let (p_eq_true, _) = split_arrow_e(&a_the)?;
        let (p_eq_false, _) = split_arrow_e(&b_the)?;
        // p_eq_true = @Eq Prop P TrueC ; recover the embedded True/False consts.
        let (t_args, _) = app_spine(&p_eq_true);
        let (f_args, _) = app_spine(&p_eq_false);
        if t_args.len() != 3 || f_args.len() != 3 {
            return None;
        }
        let true_c = &t_args[2];
        let false_c = &f_args[2];
        let rhs_e = the_at.clone();
        let lhs_e = lhs_point.clone();

        // Shared epsilon plumbing: Q, the guard subtype, its nonemptiness, the
        // chosen element, and the defining property `(∃z. pred z) → pred (THE …)`
        // — exactly the terms `isabelle.def.HOL.The α hne pred` δβ-unfolds to.
        let q = guard_pred(alpha, pred);
        let sub = subtype(alpha, &q);
        let ne_w = ne_of_guard(alpha, hne, pred);
        let choose = Expr::apps(
            Expr::const_str_levels("Classical.choice", vec![obj_level()]),
            [sub, ne_w],
        );
        let property = Expr::apps(
            Expr::const_str_levels("Subtype.property", vec![obj_level()]),
            [alpha.clone(), q, choose],
        );
        let exists_pred = |w: &Expr, wpf: Expr| {
            Expr::apps(
                Expr::const_str_levels("Exists.intro", vec![obj_level()]),
                [alpha.clone(), pred.clone(), w.clone(), wpf],
            )
        };
        let (_true_enc, true_pf) = true_enc_and_proof();
        let not_p = Expr::arrow(p.clone(), Expr::const_str("False"));
        let goal = eq_at(alpha, &lhs_e, &rhs_e);

        // ── case `h : P` ──
        let fh = FVarId::new(0x1_b301);
        let pos_arm = {
            let h = Expr::fvar(fh);
            // ite-side: If P x y = x.
            let e1 = ite_eq_branch(alpha, p, x, y, &h, true);
            // P = True by propext (mp: anything → the True inhabitant; mpr: h).
            let p_true = propext_iff(
                p.clone(),
                true_c.clone(),
                Expr::lam(BinderInfo::Default, p.clone(), true_pf.clone()),
                Expr::lam(BinderInfo::Default, true_c.clone(), h.clone()),
            );
            // pred x: first conjunct is `refl x`, second is absurd (P ∧ P=False).
            let fhf = FVarId::new(0x1_b302);
            let h2 = {
                // λ(hf : P=False). (Eq.mp P False hf h) (x = y) — the transported
                // `False` (δ `∀Q.Q`) applied at the needed conclusion.
                let hf = Expr::fvar(fhf);
                let false_val = Expr::apps(
                    Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
                    [p.clone(), false_c.clone(), hf, h.clone()],
                );
                let body = Expr::app(false_val, eq_at(alpha, x, y));
                Expr::lam(
                    BinderInfo::Default,
                    p_eq_false.clone(),
                    body.abstract_fvar(fhf),
                )
            };
            let h1 = Expr::lam(
                BinderInfo::Default,
                p_eq_true.clone(),
                Expr::apps(
                    Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                    [alpha.clone(), x.clone()],
                ),
            );
            let wx = conj_intro(&a_x, &b_x, h1, h2);
            let pt = Expr::app(property.clone(), exists_pred(x, wx));
            // THE-side: THE … = x  (first conjunct of `pred (THE …)` at P=True).
            let c1 = conj_elim(&a_the, &b_the, &pt, &eq_at(alpha, &rhs_e, x), |h1, _h2| {
                Expr::app(h1, p_true.clone())
            });
            // If P x y = x = THE …
            let body = Expr::apps(
                Expr::const_str_levels("Eq.trans", vec![obj_level()]),
                [
                    alpha.clone(),
                    lhs_e.clone(),
                    x.clone(),
                    rhs_e.clone(),
                    e1,
                    Expr::apps(
                        Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                        [alpha.clone(), rhs_e.clone(), x.clone(), c1],
                    ),
                ],
            );
            Expr::lam(BinderInfo::Default, p.clone(), body.abstract_fvar(fh))
        };

        // ── case `hn : ¬P` ──
        let fhn = FVarId::new(0x1_b401);
        let neg_arm = {
            let hn = Expr::fvar(fhn);
            // ite-side: If P x y = y.
            let e1 = ite_eq_branch(alpha, p, x, y, &hn, false);
            // P = False by propext (mp: transport hn's False; mpr: False → P).
            let fhp = FVarId::new(0x1_b402);
            let mp = {
                let hp = Expr::fvar(fhp);
                let body = Expr::apps(
                    Expr::const_str_levels("False.elim", vec![Level::zero()]),
                    [false_c.clone(), Expr::app(hn.clone(), hp)],
                );
                Expr::lam(BinderInfo::Default, p.clone(), body.abstract_fvar(fhp))
            };
            let fhf = FVarId::new(0x1_b403);
            let mpr = {
                // λ(f : FalseC). f P  — FalseC δ-unfolds to `∀Q. Q`.
                let f = Expr::fvar(fhf);
                let body = Expr::app(f, p.clone());
                Expr::lam(
                    BinderInfo::Default,
                    false_c.clone(),
                    body.abstract_fvar(fhf),
                )
            };
            let p_false = propext_iff(p.clone(), false_c.clone(), mp, mpr);
            // pred y: first conjunct is absurd (P=True yields P, contradicting
            // hn), second is `refl y`.
            let fht = FVarId::new(0x1_b404);
            let h1 = {
                // λ(ht : P=True). False.elim (y = x) (hn (Eq.mp (symm ht) trueI)).
                let ht = Expr::fvar(fht);
                let symm_ht = Expr::apps(
                    Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                    [Expr::prop(), p.clone(), true_c.clone(), ht],
                );
                let p_val = Expr::apps(
                    Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
                    [true_c.clone(), p.clone(), symm_ht, true_pf.clone()],
                );
                let body = Expr::apps(
                    Expr::const_str_levels("False.elim", vec![Level::zero()]),
                    [eq_at(alpha, y, x), Expr::app(hn.clone(), p_val)],
                );
                Expr::lam(
                    BinderInfo::Default,
                    p_eq_true.clone(),
                    body.abstract_fvar(fht),
                )
            };
            let h2 = Expr::lam(
                BinderInfo::Default,
                p_eq_false.clone(),
                Expr::apps(
                    Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                    [alpha.clone(), y.clone()],
                ),
            );
            let wy = conj_intro(&a_y, &b_y, h1, h2);
            let pt = Expr::app(property, exists_pred(y, wy));
            // THE-side: THE … = y  (second conjunct at P=False).
            let c1 = conj_elim(&a_the, &b_the, &pt, &eq_at(alpha, &rhs_e, y), |_h1, h2| {
                Expr::app(h2, p_false.clone())
            });
            let body = Expr::apps(
                Expr::const_str_levels("Eq.trans", vec![obj_level()]),
                [
                    alpha.clone(),
                    lhs_e.clone(),
                    y.clone(),
                    rhs_e.clone(),
                    e1,
                    Expr::apps(
                        Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                        [alpha.clone(), rhs_e.clone(), y.clone(), c1],
                    ),
                ],
            );
            Expr::lam(BinderInfo::Default, not_p.clone(), body.abstract_fvar(fhn))
        };

        // Excluded middle over the Prop goal.
        let or_ty = Expr::apps(Expr::const_str("Or"), [p.clone(), not_p.clone()]);
        let motive = Expr::lam(BinderInfo::Default, or_ty, goal.clone());
        let em = Expr::app(Expr::const_str("Classical.em"), p.clone());
        Some(Expr::apps(
            Expr::const_str("Or.rec"),
            [p.clone(), not_p, motive, pos_arm, neg_arm, em],
        ))
    }
}

/// Decompose an application `f a₁ … aₙ` into `([a₁,…,aₙ], f)`.
fn app_spine(e: &Expr) -> (Vec<Expr>, Expr) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = (**f).clone();
    }
    args.reverse();
    (args, cur)
}

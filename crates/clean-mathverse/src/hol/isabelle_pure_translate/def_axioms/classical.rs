// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Classical-reasoning rule proofs for the Isabelle Pure definitional-axiom
//! translator (`false_enc`, `kernel_not_to_hol_not`, `em_case_split`,
//! `prove_eq_refl_true`, `classical_rule_proof`, …). Moved verbatim from the
//! original single-file `def_axioms` module; behaviour is byte-identical.

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::super::*;
/// `true` iff `e` is exactly the `False` definition const `isabelle.def.HOL.False`
/// (the embedded form of HOL's `False`, defeq to `False_enc = ∀Q.Q`).
pub(crate) fn is_false_def_const(e: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    matches!(e.kind(), ExprKind::Const(name, _) if *name == Name::from_string("isabelle.def.HOL.False"))
}

/// `False_enc = ∀(Q:Prop). Q` — the HOL `False` encoding (matching
/// [`connective_encoding`]`("HOL.False")`), which any HOL-`False` witness inhabits
/// and from which any proposition follows by application.
pub(crate) fn false_enc() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0))
}

/// Coerce a clean-kernel negation `hnp : P → False` (the second component of
/// `Classical.em P`) into a HOL negation `Not P` (defeq `P → False_enc`):
/// `fun (hp : P) => @False.elim.{0} False_enc (hnp hp)`. `p` is the embedded `P`.
pub(crate) fn kernel_not_to_hol_not(p: &Expr, hnp: Expr) -> Expr {
    let fv = FVarId::new(0xC1A5_0001);
    let hp = Expr::fvar(fv);
    let absurd = Expr::app(hnp, hp);
    let fe = Expr::apps(
        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
        [false_enc(), absurd],
    );
    Expr::lam(BinderInfo::Default, p.clone(), fe.abstract_fvar(fv))
}

/// Build `@Or.rec P (P→False) (fun _ => goal) pos neg (Classical.em P)`, the
/// case-split on excluded middle used by every classical-reasoning rule. `pos`
/// proves `goal` from `hp : P`; `neg` proves `goal` from `hnp : P → False`
/// (clean-kernel negation). The motive is the constant family `fun _ => goal`.
pub(crate) fn em_case_split(p: &Expr, goal: &Expr, pos: Expr, neg: Expr) -> Expr {
    let not_p_kernel = Expr::arrow(p.clone(), Expr::const_str("False"));
    let em = Expr::app(Expr::const_str("Classical.em"), p.clone());
    let or_ty = Expr::apps(Expr::const_str("Or"), [p.clone(), not_p_kernel.clone()]);
    let motive = Expr::lam(BinderInfo::Default, or_ty, goal.clone());
    Expr::apps(
        Expr::const_str("Or.rec"),
        [p.clone(), not_p_kernel, motive, pos, neg, em],
    )
}

/// Statement-level proof of Isabelle's `Metis.not_atomize`, the meta-logic
/// *atomize-negation* rule
///
/// ```text
/// (¬A ⟹ False) ≡ A
/// ```
///
/// — a `Pure.eq` (propositional equality, `@Eq Prop`) between the Pure-level
/// statement `(HOL.Not A ⟹ HOL.False)` and the HOL proposition `A`. Under this
/// embedding the LHS is `(Not A → False)` (where `Not A` defeq `A → False_enc`
/// and `False` defeq `False_enc = ∀R.R`) and the RHS is `A`. The two sides are
/// propositionally — but not definitionally — equal, so the proof goes through
/// `propext` of a classically-proved `Iff`, exactly like the [`classical_rule_proof`]
/// family (`Classical.em` + `propext`, foundational closure). It is NOT the
/// recorded def-raw proof (which references export-absent atomize lemmas).
///
/// `prop` is the embedded statement **before** the schematic-variable
/// quantification that `translate_theorem` performs at the end (so the HOL
/// `?A::bool` is still a *free fvar* `A`, not yet a leading `∀(A:Prop)` binder).
/// The recognized shape is
///
/// ```text
/// @Eq Prop ((isabelle.def.HOL.Not A) → isabelle.def.HOL.False) A
/// ```
///
/// where `A` is an arbitrary `Prop` subterm (the schematic-variable fvar). On a
/// match the proof body `propext (Not A → False) A (Iff.intro mp mpr)` — which
/// **mentions that same `A`** so the outer `term_params` lambda-wrapping in
/// `translate_theorem` binds it correctly — is returned, where
///   - `mp  : (Not A → False) → A` is `ccontr` (`em A`: A-branch returns `hp`;
///     ¬A-branch coerces the kernel negation to `Not A`, applies the premise to
///     get `False`/`∀R.R`, applies that to `A`);
///   - `mpr : A → (Not A → False)` is `λ(ha:A)(hn:Not A). hn ha` (`hn ha :
///     False_enc`, defeq `isabelle.def.HOL.False`).
///
/// Returns `None` if the statement is not this shape. The kernel re-checks the
/// produced term against the embedded statement, so a wrong match is rejected —
/// never miscounted.
pub(crate) fn prove_not_atomize(prop: &Expr) -> Option<Expr> {
    // The statement must be `@Eq Prop LHS A` with
    // `LHS = (isabelle.def.HOL.Not A → isabelle.def.HOL.False)`.
    let (alpha, lhs, a) = eq_three_parts(prop)?;
    if alpha != Expr::prop() {
        return None;
    }
    // LHS is an arrow `(Not A) → False_def`.
    let (not_a, false_cod) = split_arrow(&lhs)?;
    if !is_false_def_const(&false_cod) {
        return None;
    }
    // `Not A`'s argument must equal the equation's RHS `A`.
    let inner = hol_not_arg(&not_a)?;
    if inner != a {
        return None;
    }
    // `A` may itself be any closed `Prop` subterm (the schematic-variable fvar).
    // Build the proof referencing that exact `A`; the implication premises (of
    // `mp`/`mpr`) are tracked by fresh fvars so `abstract_fvar` handles their de
    // Bruijn bookkeeping.
    let hol_not_a = not_def_applied(&a); // isabelle.def.HOL.Not A
    let false_def = Expr::const_str("isabelle.def.HOL.False");
    let lhs_a = Expr::arrow(hol_not_a.clone(), false_def); // (Not A) → False

    // mp : (Not A → False) → A  (this is `ccontr` over `A`).
    let mp = {
        let fh = FVarId::new(0xA701_0002);
        let h = Expr::fvar(fh); // h : Not A → False_def
                                // pos branch (A holds): `fun (hp : A) => hp`.
        let fhp = FVarId::new(0xA701_0003);
        let pos = {
            let hp = Expr::fvar(fhp);
            Expr::lam(BinderInfo::Default, a.clone(), hp.abstract_fvar(fhp))
        };
        // neg branch (¬A holds): coerce kernel `hna : A → False` to HOL `Not A`,
        // apply `h` to it (: False_def, defeq `∀R.R`), apply to `A` for the goal.
        let fhna = FVarId::new(0xA701_0004);
        let neg = {
            let hna = Expr::fvar(fhna);
            let hol_not = kernel_not_to_hol_not(&a, hna.clone()); // : Not A
            let applied = Expr::app(h.clone(), hol_not); // : False_def (defeq ∀R.R)
            let goal_a = Expr::app(applied, a.clone()); // : A
            Expr::lam(
                BinderInfo::Default,
                Expr::arrow(a.clone(), Expr::const_str("False")),
                goal_a.abstract_fvar(fhna),
            )
        };
        let case = em_case_split(&a, &a, pos, neg);
        Expr::lam(BinderInfo::Default, lhs_a.clone(), case.abstract_fvar(fh))
    };

    // mpr : A → (Not A → False)  is `fun (ha:A)(hn:Not A) => hn ha`.
    let mpr = {
        let fha = FVarId::new(0xA701_0005);
        let fhn = FVarId::new(0xA701_0006);
        let ha = Expr::fvar(fha);
        let hn = Expr::fvar(fhn);
        let applied = Expr::app(hn, ha); // hn ha : False_enc, defeq False_def
        let inner_lam = Expr::lam(
            BinderInfo::Default,
            hol_not_a.clone(),
            applied.abstract_fvar(fhn),
        );
        Expr::lam(BinderInfo::Default, a.clone(), inner_lam.abstract_fvar(fha))
    };

    // propext (Not A → False) A (Iff.intro …): the equation `@Eq Prop lhs_a A`.
    // The body mentions `A` (the schematic fvar); the surrounding `translate_theorem`
    // wrapping abstracts it into the leading `∀(A:Prop)` binder.
    Some(propext_iff(lhs_a, a, mp, mpr))
}

/// `isabelle.def.HOL.Not` applied to one argument (`Not a`), the embedded HOL
/// negation. Defeq `a → False_enc`.
pub(crate) fn not_def_applied(a: &Expr) -> Expr {
    Expr::app(Expr::const_str("isabelle.def.HOL.Not"), a.clone())
}

/// Statement-level proof of Isabelle's `HOL.simp_thms_6`, the simp normal-form
/// rewrite
///
/// ```text
/// (x = x) = True
/// ```
///
/// (often under a leading `OFCLASS('a, type_class)` sort constraint). The embedded
/// statement is `(True →)* @Eq Prop (@Eq α a a) isabelle.def.HOL.True`. This is
/// `eqTrueI` applied to reflexivity: by `propext` of `(a = a) ↔ True`,
///   - `mp  : (a = a) → True` is `λ_. true_refl`;
///   - `mpr : True → (a = a)` is `λ_. @Eq.refl α a`.
/// Each leading `True` premise (an erased `OFCLASS`) is discharged by an enclosing
/// `fun (_:True) =>`. Built from `propext`/`Eq.refl` only (foundational closure);
/// the kernel re-checks against the embedded statement, so a wrong match is
/// rejected — never miscounted.
pub(crate) fn prove_eq_refl_true(prop: &Expr) -> Option<Expr> {
    use clean_kernel::expr::ExprKind;
    // Peel leading `True →` premises (erased `OFCLASS` sort constraints).
    let mut n_true = 0usize;
    let mut cur = prop.clone();
    while let ExprKind::Pi(_, dom, cod) = cur.kind() {
        if **dom != Expr::const_str("True") {
            break;
        }
        n_true += 1;
        cur = (**cod).clone();
    }
    // Conclusion must be `@Eq Prop (@Eq α a a) isabelle.def.HOL.True`.
    let (alpha_outer, lhs, rhs) = eq_three_parts(&cur)?;
    if alpha_outer != Expr::prop() {
        return None;
    }
    if !is_true_def_const(&rhs) {
        return None;
    }
    // LHS is an inner reflexive equation `@Eq α a a`.
    let (alpha, a, b) = eq_three_parts(&lhs)?;
    if a != b {
        return None;
    }
    // mp : (a = a) → True_def  is `fun _ => true_refl` (`true_refl` is closed).
    let (_, true_refl) = true_enc_and_proof();
    let mp = Expr::lam(BinderInfo::Default, lhs.clone(), true_refl);
    // mpr : True_def → (a = a)  is `fun _ => @Eq.refl α a`.
    let refl = Expr::apps(
        Expr::const_str_levels("Eq.refl", vec![obj_level()]),
        [alpha, a],
    );
    let mpr = Expr::lam(BinderInfo::Default, rhs.clone(), refl);
    // propext (a = a) True_def (Iff.intro mp mpr).
    let mut body = propext_iff(lhs, rhs, mp, mpr);
    // Re-wrap one `fun (_:True) =>` per peeled leading premise.
    for _ in 0..n_true {
        body = Expr::lam(BinderInfo::Default, Expr::const_str("True"), body);
    }
    Some(body)
}

/// Build the complete kernel proof of a HOL classical-reasoning rule directly
/// from its embedded statement (premise propositions + conclusion), discharged by
/// `Classical.em` + `propext` (foundational closure) rather than the intricate
/// recorded def-raw proof. Returns the fully premise-lambda-wrapped term, or
/// `None` if the statement is not one of the recognized classical shapes. The
/// kernel re-checks the result against the embedded statement, so a wrong match is
/// rejected — never miscounted.
///
/// Recognized shapes (`Not Q ≡ isabelle.def.HOL.Not Q`, defeq `Q → False_enc`;
/// `False ≡ isabelle.def.HOL.False`, defeq `False_enc = ∀R.R`):
///   - `eqTrueI`:   `P ⟹ (P = True)`.
///   - `classical`: `(Not P ⟹ P) ⟹ P`.
///   - `ccontr`:    `(Not P ⟹ False) ⟹ P`.
///   - `swap`:      `Not P ⟹ (Not Q ⟹ P) ⟹ Q`.
pub(crate) fn classical_rule_proof(premise_tys: &[Expr], concl_e: &Expr) -> Option<Expr> {
    // Wrap a body in the premise lambdas (outermost premise binds first); the body
    // is built closed (all fvars abstracted), so it is independent of the wrapping.
    let wrap = |body: Expr| -> Expr {
        let mut e = body;
        for ty in premise_tys.iter().rev() {
            e = Expr::lam(BinderInfo::Default, ty.clone(), e);
        }
        e
    };
    // Premise fvar handles (one per premise binder), in declaration order.
    let prem_fvar = |pos: usize| FVarId::new(0xC1A5_1000 + pos as u64);
    let prem = |pos: usize| Expr::fvar(prem_fvar(pos));
    // Abstract every premise fvar in `body`, innermost-last (so positions line up
    // with `wrap`'s outermost-first lambdas).
    let abstract_prems = |mut body: Expr| -> Expr {
        for pos in 0..premise_tys.len() {
            body = body.abstract_fvar(prem_fvar(pos));
        }
        body
    };

    // ── Isabelle `abs_cong`-shaped λ-congruence ───────────────────────────────
    // `⟦sort…⟧ ⟹ (⋀x. f x = g x) ⟹ (λx. f x) = (λx. g x)`: the two λ-abstraction
    // operands are proved equal DIRECTLY by `funext` applied to the pointwise
    // hypothesis (the LAST premise). Any leading premises — the `OFCLASS(_,type)`
    // sort constraints, embedded to `True` — are bound and ignored. `funext`'s
    // transitive axiom closure is foundational (⊆ {Quot.sound, propext,
    // Classical.choice, Eq built-ins}). The recorded proofs of these anonymous
    // derivation boxes collapse to a `True`-typed term (kernel reject
    // `expected=Pi[1]->Eq got=True`); this arm supplies the real inhabitant. The
    // kernel re-checks the built term against the stored `@Eq (α→β) (λx.f x)
    // (λx.g x)` type (up to β-η), so a mis-shape is rejected — never miscounted.
    // SHAPE-gated (both `@Eq` operands are `λ`s, the final premise a `Π` over the
    // conclusion's domain `α`), so it fires only on this congruence family.
    {
        use clean_kernel::expr::ExprKind;
        if let Some((fun_ty, l, r)) = eq_three_parts(concl_e) {
            if let ExprKind::Pi(_, alpha, beta) = fun_ty.kind() {
                let both_lam =
                    matches!(l.kind(), ExprKind::Lam(..)) && matches!(r.kind(), ExprKind::Lam(..));
                if both_lam && !premise_tys.is_empty() {
                    let hyp_pos = premise_tys.len() - 1;
                    if let ExprKind::Pi(_, hyp_dom, _) = premise_tys[hyp_pos].kind() {
                        if **hyp_dom == **alpha {
                            let alpha_e = (**alpha).clone();
                            // Constant codomain family `λ(_:α). β` (β is the arrow's
                            // codomain; for the non-dependent function type it is
                            // closed under the binder, so the clone is a valid body).
                            let fam =
                                Expr::lam(BinderInfo::Default, alpha_e.clone(), (**beta).clone());
                            let body = Expr::apps(
                                Expr::const_str_levels("funext", vec![obj_level(), obj_level()]),
                                [alpha_e, fam, l.clone(), r.clone(), prem(hyp_pos)],
                            );
                            return Some(wrap(abstract_prems(body)));
                        }
                    }
                }
            }
        }
    }

    match premise_tys.len() {
        1 => {
            let p0 = &premise_tys[0];
            // eqTrueI: premise `P`, conclusion `@Eq Prop P True_enc`.
            if let Some((alpha, lhs, rhs)) = eq_three_parts(concl_e) {
                if alpha == Expr::prop() && lhs == *p0 && is_true_def_const(&rhs) {
                    let (_, true_refl) = true_enc_and_proof();
                    // propext P True (fun _:P => true_refl) (fun _:True => hp)
                    let fwd = Expr::lam(BinderInfo::Default, p0.clone(), true_refl);
                    let bwd = Expr::lam(BinderInfo::Default, rhs.clone(), prem(0));
                    let body = propext_iff(lhs, rhs, fwd, bwd);
                    return Some(wrap(abstract_prems(body)));
                }
            }
            // classical: premise `Not P → P`, conclusion `P`.
            // ccontr:    premise `Not P → False`, conclusion `P`.
            let (dom, cod) = split_arrow(p0)?;
            let p = hol_not_arg(&dom)?;
            if *concl_e != p {
                return None;
            }
            // pos branch: `fun (hp : P) => hp`.
            let fhp = FVarId::new(0xC1A5_2001);
            let pos = {
                let hp = Expr::fvar(fhp);
                Expr::lam(BinderInfo::Default, p.clone(), hp.abstract_fvar(fhp))
            };
            // neg branch: `fun (hnp : P → False) => <discharge>`.
            let fhnp = FVarId::new(0xC1A5_2002);
            let hnp = Expr::fvar(fhnp);
            let hol_not = kernel_not_to_hol_not(&p, hnp.clone());
            let applied = Expr::app(prem(0), hol_not); // h (Not P) : cod
            let discharged = if cod == p {
                // classical: `cod = P`, so `h (Not P) : P` is the goal directly.
                applied
            } else if is_false_def_const(&cod) {
                // ccontr: `cod = False` (defeq `False_enc = ∀R.R`), so apply to `P`.
                Expr::app(applied, p.clone())
            } else {
                return None;
            };
            let neg = Expr::lam(
                BinderInfo::Default,
                Expr::arrow(p.clone(), Expr::const_str("False")),
                discharged.abstract_fvar(fhnp),
            );
            let body = em_case_split(&p, concl_e, pos, neg);
            Some(wrap(abstract_prems(body)))
        }
        2 => {
            // Boolean case-analysis twins for proving `P = Q` (early-HOL bootstrap
            // lemmas; the anonymous derivation-box family under Pure's `iff`
            // reasoning). Both have conclusion `@Eq Prop P Q` and premise0 an
            // `@Eq Prop P {True,False}_def` — a SHAPE gate, no name gate (they are
            // anonymous boxes). The recorded proofs reconstruct the boolean
            // congruence via an `equal_elim` tower that leaks a schematic
            // (`expected=Sort got=FVar`, the phantom-parameter wall), so they
            // reject; discharging by `propext` sidesteps the tower. Foundational
            // (`propext`/`Eq.{mp,symm}`/`Iff.intro`), and the kernel re-checks the
            // built term against `@Eq Prop P Q`, so a mis-shape is rejected — never
            // miscounted. These two co-gate essentially the whole early-HOL cascade.
            //
            //   - eq-True forward: `(P = True) ⟹ (P ⟹ Q) ⟹ (P = Q)`.
            //       From `P = True`, `P` holds (`Eq.mp (symm h0) true_refl`), so
            //       `Q ⟹ P` is `λ_. that`, and `P ⟹ Q` is premise1 → `propext`.
            //   - eq-False: `(P = False) ⟹ (Q ⟹ P) ⟹ (P = Q)`.
            //       From `P = False`, `P ⟹ Q` is `λp. (Eq.mp h0 p) Q` (the
            //       transported `False ≡ ∀R.R` applied at `Q`), and `Q ⟹ P` is
            //       premise1 → `propext`.
            if let Some((alpha_c, p_c, q_c)) = eq_three_parts(concl_e) {
                if alpha_c == Expr::prop() {
                    if let Some((alpha0, lhs0, rhs0)) = eq_three_parts(&premise_tys[0]) {
                        if alpha0 == Expr::prop() && lhs0 == p_c {
                            // eq-True forward: premise1 must be `P → Q`.
                            if is_true_def_const(&rhs0) {
                                if let Some((d1, c1)) = split_arrow(&premise_tys[1]) {
                                    if d1 == p_c && c1 == q_c {
                                        let (_, true_refl) = true_enc_and_proof();
                                        // symm h0 : True_def = P
                                        let symm = Expr::apps(
                                            Expr::const_str_levels("Eq.symm", vec![obj_level()]),
                                            [Expr::prop(), p_c.clone(), rhs0.clone(), prem(0)],
                                        );
                                        // pP : P  = Eq.mp True_def P (symm h0) true_refl
                                        let p_pf = Expr::apps(
                                            Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
                                            [rhs0.clone(), p_c.clone(), symm, true_refl],
                                        );
                                        // fwd : P → Q = premise1; bwd : Q → P = λ_:Q. pP.
                                        let fwd = prem(1);
                                        let bwd = Expr::lam(BinderInfo::Default, q_c.clone(), p_pf);
                                        let body = propext_iff(p_c, q_c, fwd, bwd);
                                        return Some(wrap(abstract_prems(body)));
                                    }
                                }
                            }
                            // eq-False: premise1 must be `Q → P`.
                            if is_false_def_const(&rhs0) {
                                if let Some((d1, c1)) = split_arrow(&premise_tys[1]) {
                                    if d1 == q_c && c1 == p_c {
                                        // notP : P → False_def = Eq.mp P False_def h0 (3 args).
                                        let not_p = Expr::apps(
                                            Expr::const_str_levels("Eq.mp", vec![Level::zero()]),
                                            [p_c.clone(), rhs0.clone(), prem(0)],
                                        );
                                        // fwd : P → Q = λ hp:P. (notP hp) Q.
                                        let fhp = FVarId::new(0xC1A5_4001);
                                        let hp = Expr::fvar(fhp);
                                        let applied = Expr::app(Expr::app(not_p, hp), q_c.clone());
                                        let fwd = Expr::lam(
                                            BinderInfo::Default,
                                            p_c.clone(),
                                            applied.abstract_fvar(fhp),
                                        );
                                        // bwd : Q → P = premise1.
                                        let bwd = prem(1);
                                        let body = propext_iff(p_c, q_c, fwd, bwd);
                                        return Some(wrap(abstract_prems(body)));
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // swap (`¬P ⟹ (¬Q ⟹ P) ⟹ Q`): premise0 `Not P`, premise1 `Not Q → P`,
            // conclusion `Q`. Proof by `em Q`:
            //   - Q holds (hq):       goal `Q` is `hq`.
            //   - ¬Q holds (hnq_k):   `hol_not_q = fun hq => False.elim (hnq_k hq)`;
            //       `premise1 hol_not_q : P`; `premise0 (that) : False_enc`; apply to
            //       `Q` for the goal.
            let p0 = &premise_tys[0];
            let p1 = &premise_tys[1];
            let q = concl_e;
            // premise0 must be `Not P` for some P.
            let p = hol_not_arg(p0)?;
            // premise1 must be `Not Q → P` (same P), with Q = conclusion.
            let (dom1, cod1) = split_arrow(p1)?;
            let q_of_not = hol_not_arg(&dom1)?;
            if q_of_not != *q || cod1 != p {
                return None;
            }
            // pos branch (Q holds): `fun (hq : Q) => hq`.
            let fhq = FVarId::new(0xC1A5_3001);
            let pos_q = {
                let hq = Expr::fvar(fhq);
                Expr::lam(BinderInfo::Default, q.clone(), hq.abstract_fvar(fhq))
            };
            // neg branch (¬Q holds): premise1 (Not Q) → P, premise0 (Not P) →
            // False_enc, apply to Q.
            let fhnq = FVarId::new(0xC1A5_3002);
            let neg_q = {
                let hnq = Expr::fvar(fhnq);
                let hol_not_q = kernel_not_to_hol_not(q, hnq.clone());
                let p_val = Expr::app(prem(1), hol_not_q); // : P
                let false_enc_val = Expr::app(prem(0), p_val); // : False_enc
                let body = Expr::app(false_enc_val, q.clone()); // : Q
                Expr::lam(
                    BinderInfo::Default,
                    Expr::arrow(q.clone(), Expr::const_str("False")),
                    body.abstract_fvar(fhnq),
                )
            };
            let body = em_case_split(q, q, pos_q, neg_q);
            Some(wrap(abstract_prems(body)))
        }
        _ => None,
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Point-free HOL logical/instance definitional axioms — the `…_def_raw`
//! equations whose LHS is the **bare** defined constant `C` (NOT applied to its
//! arguments) and whose RHS is a lambda spelling `C`'s body:
//!
//! ```text
//! HOL.Ex             ≡ (λP. ∀Q. (∀x. P x ⟶ Q) ⟶ Q)
//! HOL.Uniq           ≡ (λP. ∀x y. P x ⟶ P y ⟶ x = y)
//! HOL.Ex1            ≡ (λP. ∃x. P x ∧ (∀y. P y ⟶ y = x))
//! HOL.Let            ≡ (λs f. f s)
//! HOL.induct_forall  ≡ (λP. ∀x. P x)
//! HOL.induct_equal   ≡ (λx y. x = y)
//! HOL.NO_MATCH       ≡ (λpat val. True)
//! HOL.All            ≡ (λP. P = (λx. True))
//! ```
//!
//! These arise as the point-free companions of the *applied* `All_def`/`Ex_def`
//! equations already handled by [`super::all_def_predicate`] /
//! [`super::ex_def_predicate`]; the raw export re-states each definition point-free
//! (LHS `C`, RHS `λargs. body`) inside an unnamed consumer whose recorded proof
//! bottoms out at the un-mappable `…_def_raw` `PAxm` leaf. Rather than translate
//! that leaf, we prove the whole embedded statement directly:
//!
//! - build `lhs_sem` by embedding the **η-expanded** applied form
//!   `λargs. C a₁ … aₙ` (which routes through the existing `HOL.Ex`/`HOL.All`/`=`/…
//!   embedding arms to `C`'s faithful semantic meaning — the SAME clean term the
//!   applied `…_def` LHS produces);
//! - build `rhs` by embedding the recorded body `λargs. body`;
//! - store the REAL equation `@Eq T lhs_sem rhs` (two DISTINCT source terms — never
//!   a `B = B` tautology) and prove it either by `Eq.refl` (when `lhs_sem` δβ-reduces
//!   to `rhs`, i.e. every case except `All`) or by a `funext`/`propext` bridge (the
//!   `All` case, where `∀x. P x` is only *propositionally* equal to `P = λx.True`).
//!
//! The kernel re-checks the produced term against the stored equation, so a
//! mis-embedding is rejected — never miscounted. `If`/`the_eq_trivial` are NOT
//! handled here: their bodies irreducibly need `HOL.The` (Hilbert definite
//! description) with no closed clean image, so they are left unmapped.

use clean_kernel::expr::FVarId;
use clean_kernel::{BinderInfo, Expr};

use super::super::super::isabelle_pure::{IsaProvenTheorem, IsaTerm, IsaType};
use super::*;

/// Whether `name` is a point-free HOL logical constant this module maps. Every one
/// of these has a `…_def_raw` axiom of the shape `Pure.eq C (λargs. body)`; the
/// applied-form companions (`All_def`, `Ex_def`) are handled elsewhere, but the
/// point-free re-statement lands here.
pub(crate) fn is_pointfree_def_const(name: &str) -> bool {
    matches!(
        name,
        "HOL.All"
            | "HOL.Ex"
            | "HOL.Uniq"
            | "HOL.Ex1"
            | "HOL.Let"
            | "HOL.induct_forall"
            | "HOL.induct_equal"
            | "HOL.NO_MATCH"
            | "ATP.fFalse"
            | "ATP.fTrue"
            | "ATP.fNot"
            | "ATP.fconj"
            | "ATP.fdisj"
            | "ATP.fimplies"
            | "ATP.fAll"
            | "ATP.fEx"
            | "ATP.fequal"
            | "ATP.fComp"
            | "ATP.fChoice"
    )
}

/// The ATP aliases whose `…_def_raw` RHS is a **bare constant** rather than a
/// lambda (`fFalse ≡ False`, `fTrue ≡ True`, `fChoice ≡ Eps`) — the 0-ary case
/// [`pointfree_def_parts`] admits without an `Abs` RHS.
pub(crate) fn is_bare_alias_pointfree(name: &str) -> bool {
    matches!(name, "ATP.fFalse" | "ATP.fTrue" | "ATP.fChoice")
}

/// If `thm`'s conclusion (after stripping the leading `type_class` sort-constraint
/// premises) is a **point-free** definitional equation `Pure.eq C (λargs. body)`
/// whose LHS is one of the [`is_pointfree_def_const`] bare constants, return
/// `(const_name, const_type, rhs_lambda)`. The RHS must be a lambda (`Abs`), which
/// carries the argument types the η-expansion needs — except for the 0-ary ATP
/// bare aliases ([`is_bare_alias_pointfree`]), whose RHS is the aliased constant.
pub(crate) fn pointfree_def_parts(thm: &IsaProvenTheorem) -> Option<(&str, &IsaType, &IsaTerm)> {
    let concl = strip_leading_imps(&thm.prop);
    let (lhs, rhs) = pure_eq_parts(concl)?;
    // LHS must be the BARE constant (no application spine).
    let IsaTerm::Const { n, t } = lhs else {
        return None;
    };
    if !is_pointfree_def_const(n) {
        return None;
    }
    // RHS must be a lambda telescope (`λargs. body`) — it carries the arg types —
    // EXCEPT for the 0-ary ATP aliases (`fFalse ≡ False`, `fTrue ≡ True`,
    // `fChoice ≡ Eps`), whose RHS is the bare aliased constant.
    let abs_rhs = matches!(rhs, IsaTerm::Abs { .. });
    let bare_alias_rhs = is_bare_alias_pointfree(n) && matches!(rhs, IsaTerm::Const { .. });
    if !abs_rhs && !bare_alias_rhs {
        return None;
    }
    Some((n.as_str(), t, rhs))
}

impl Ctx {
    /// Prove a point-free `…_def_raw` equation `Pure.eq C (λargs. body)`.
    ///
    /// Builds `lhs_sem` = embedding of the η-expanded applied form
    /// `λ(a₁:T₁)…(aₙ:Tₙ). C a₁ … aₙ` (the SAME clean term `C`'s applied `…_def` LHS
    /// yields), and `rhs` = embedding of the recorded body, then proves
    /// `@Eq (T₁→…→R) lhs_sem rhs`. Every case is reflexive under the embedding
    /// EXCEPT `HOL.All`, whose semantic meaning `λP. ∀x. P x` is only
    /// propositionally (not definitionally) equal to `λP. P = (λx.True)`; that case
    /// routes through the pointwise [`all_def_bridge_proof`] lifted across `funext`.
    ///
    /// Returns the `(stored_type, proof)` pair, discharging each leading
    /// `type_class` sort constraint (embedded as a vacuous `True`) with an enclosing
    /// `fun (_:True) => …` on the proof and a matching `True →` arrow on the type.
    /// `binders` is the theorem's embedding binder stack (empty at the top level);
    /// the schematic predicate/argument variables in `rhs` are discovered as term
    /// parameters during embedding and quantified by the caller.
    pub(crate) fn prove_pointfree_def_raw(
        &mut self,
        thm: &IsaProvenTheorem,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<(Expr, Expr)>, TranslateError> {
        let Some((name, const_ty, rhs_lam)) = pointfree_def_parts(thm) else {
            return Ok(None);
        };
        // Collect the RHS lambda's leading binder types (the constant's argument
        // types), stopping at the body. These are the η-expansion domains.
        let mut arg_tys: Vec<IsaType> = Vec::new();
        let mut cur = rhs_lam;
        while let IsaTerm::Abs { t, b, .. } = cur {
            arg_tys.push(t.clone());
            cur = b;
        }
        // Empty `arg_tys` is the 0-ary bare-alias case (`fFalse ≡ False`,
        // `fChoice ≡ Eps` — [`is_bare_alias_pointfree`], the only shape
        // [`pointfree_def_parts`] admits without an `Abs` RHS): the "η-expansion"
        // is the bare constant itself and the equation is between two constants.
        // Build the η-expanded applied IsaTerm `λ(a₁:T₁)…(aₙ:Tₙ). C (Bound n-1) …
        // (Bound 0)`, with `C` at its full instantiated type. Embedding this routes
        // `C a₁ … aₙ` through the existing applied arms (`HOL.Ex`→ex_encoding,
        // `HOL.All`→∀-Pi, `HOL.eq`→@Eq, `HOL.True`→def-const, …), giving `C`'s
        // faithful semantic meaning.
        let eta = build_eta_expansion(name, const_ty, &arg_tys);
        let lhs_sem = self.embed_term(&eta, binders)?;
        let rhs = self.embed_term(rhs_lam, binders)?;
        // The equation's operand type `T₁ → … → Tₙ → R` — recover it as the RHS
        // lambda's inferred type (a total, non-dependent HOL function type).
        let fun_ty = self.infer_type(rhs_lam, binders)?;
        let stored_eq = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [fun_ty.clone(), lhs_sem.clone(), rhs.clone()],
        );
        // The proof: `All` needs the propext/funext bridge; every other constant is
        // reflexive (its η-expanded semantic form δβ-reduces to the embedded body).
        let core = if name == "HOL.All" {
            // `lhs_sem = λP. ∀x. P x`, `rhs = λP. P = (λx.True)`; not defeq. Lift the
            // pointwise `all_def_bridge_proof(α, P)` across `funext`. α is the
            // predicate's domain, read from the single argument type `α ⇒ bool`.
            all_def_pointfree_bridge(self, &arg_tys, &lhs_sem, &rhs)?
        } else {
            Expr::apps(
                Expr::const_str_levels("Eq.refl", vec![obj_level()]),
                [fun_ty, lhs_sem],
            )
        };
        // Discharge each leading `type_class` sort-constraint premise in lockstep.
        let n_premises = leading_premises(&thm.prop).len();
        let mut proof = core;
        let mut ty = stored_eq;
        for _ in 0..n_premises {
            proof = Expr::lam(BinderInfo::Default, Expr::const_str("True"), proof);
            ty = Expr::arrow(Expr::const_str("True"), ty);
        }
        Ok(Some((ty, proof)))
    }
}

/// Build the η-expansion `λ(a₁:T₁)…(aₙ:Tₙ). C a₁ … aₙ` of the bare constant `C`
/// (at its full type `const_ty`), with argument types `arg_tys` in order. Each
/// bound argument is referenced by its de Bruijn `Bound` index (innermost binder
/// = `Bound 0`), matching the [`IsaTerm::Bound`] convention.
fn build_eta_expansion(name: &str, const_ty: &IsaType, arg_tys: &[IsaType]) -> IsaTerm {
    let n = arg_tys.len();
    // Applied spine: C (Bound n-1) (Bound n-2) … (Bound 0).
    let mut body = IsaTerm::Const {
        n: name.to_string(),
        t: const_ty.clone(),
    };
    for j in 0..n {
        body = IsaTerm::App {
            f: Box::new(body),
            a: Box::new(IsaTerm::Bound {
                i: (n - 1 - j) as i64,
            }),
        };
    }
    // Wrap the argument binders outermost-first.
    let mut eta = body;
    for ty in arg_tys.iter().rev() {
        eta = IsaTerm::Abs {
            n: "eta".to_string(),
            t: ty.clone(),
            b: Box::new(eta),
        };
    }
    eta
}

// ---------------------------------------------------------------------------
// Leaf-reference reconstruction (`bootstrap.rs` path).
//
// When a `…_def_raw` axiom is referenced as a **leaf** (`axm`) inside another
// consumer's proof (rather than as the whole point-free consumer theorem), the
// leaf carries only its `tyinst` (the object type `'a`). We reconstruct the FULL
// point-free equation `Pure.eq C (λargs. body)` as an `IsaTerm` from `'a`, wrap it
// as a synthetic `IsaProvenTheorem`, and reuse [`Ctx::prove_pointfree_def_raw`] —
// so the leaf resolves to a kernel-checked proof of exactly the raw axiom's
// statement, and any dependent that references it resolves.
// ---------------------------------------------------------------------------

/// HOL `bool` (which embeds to clean `Prop`).
fn ty_bool() -> IsaType {
    IsaType::Type {
        n: "HOL.bool".to_string(),
        a: Vec::new(),
    }
}

/// `α ⇒ β`.
fn ty_fun(a: IsaType, b: IsaType) -> IsaType {
    IsaType::Type {
        n: "fun".to_string(),
        a: vec![a, b],
    }
}

/// A `Const` at a given type.
fn cst(n: &str, t: IsaType) -> IsaTerm {
    IsaTerm::Const {
        n: n.to_string(),
        t,
    }
}

/// `f $ a`.
fn app(f: IsaTerm, a: IsaTerm) -> IsaTerm {
    IsaTerm::App {
        f: Box::new(f),
        a: Box::new(a),
    }
}

/// `λ(_:t). b`.
fn abs(t: IsaType, b: IsaTerm) -> IsaTerm {
    IsaTerm::Abs {
        n: "x".to_string(),
        t,
        b: Box::new(b),
    }
}

/// A de Bruijn `Bound i`.
fn bnd(i: i64) -> IsaTerm {
    IsaTerm::Bound { i }
}

/// `HOL.implies a b` (`bool ⇒ bool ⇒ bool`).
fn imp(a: IsaTerm, b: IsaTerm) -> IsaTerm {
    let imp_c = cst(
        "HOL.implies",
        ty_fun(ty_bool(), ty_fun(ty_bool(), ty_bool())),
    );
    app(app(imp_c, a), b)
}

/// `HOL.eq a b` at object type `alpha` (`α ⇒ α ⇒ bool`).
fn heq(alpha: &IsaType, a: IsaTerm, b: IsaTerm) -> IsaTerm {
    let eq_c = cst(
        "HOL.eq",
        ty_fun(alpha.clone(), ty_fun(alpha.clone(), ty_bool())),
    );
    app(app(eq_c, a), b)
}

/// `HOL.All (λ(_:t). body)` (`(t ⇒ bool) ⇒ bool`).
fn all(t: IsaType, body: IsaTerm) -> IsaTerm {
    let all_c = cst("HOL.All", ty_fun(ty_fun(t.clone(), ty_bool()), ty_bool()));
    app(all_c, abs(t, body))
}

/// The RHS body lambda `λargs. body` of a point-free `…_def_raw` equation, over
/// object type `alpha`, or `None` for a name whose body needs `HOL.The` (handled
/// elsewhere). Matches the raw export forms exactly (see the module doc-comment).
fn raw_def_rhs(name: &str, alpha: &IsaType) -> Option<IsaTerm> {
    let pred_ty = ty_fun(alpha.clone(), ty_bool());
    match name {
        // λP. HOL.eq P (λx. True)   — the eq-trick definition of ∀.
        "HOL.All" => {
            let lam_true = abs(alpha.clone(), cst("HOL.True", ty_bool()));
            let pred_eq = cst(
                "HOL.eq",
                ty_fun(pred_ty.clone(), ty_fun(pred_ty.clone(), ty_bool())),
            );
            Some(abs(pred_ty, app(app(pred_eq, bnd(0)), lam_true)))
        }
        // λP. ∀Q:bool. (∀x. P x ⟶ Q) ⟶ Q
        "HOL.Ex" => {
            // Under binders [P(=B..), Q, x]: P is Bound 2 at the ∀x body, Q is Bound 1.
            let px = app(bnd(2), bnd(0)); // P x
            let inner = all(alpha.clone(), imp(px, bnd(1))); // ∀x. P x ⟶ Q
            let body = all(ty_bool(), imp(inner, bnd(0))); // ∀Q. inner ⟶ Q
            Some(abs(pred_ty, body))
        }
        // λP. ∀x y. P x ⟶ P y ⟶ x = y
        "HOL.Uniq" => {
            // Under [P, x, y]: P=Bound 2, x=Bound 1, y=Bound 0.
            let px = app(bnd(2), bnd(1));
            let py = app(bnd(2), bnd(0));
            let eqxy = heq(alpha, bnd(1), bnd(0));
            let inner = imp(px, imp(py, eqxy));
            let body = all(alpha.clone(), all(alpha.clone(), inner));
            Some(abs(pred_ty, body))
        }
        // λP. ∃x. P x ∧ (∀y. P y ⟶ y = x)
        "HOL.Ex1" => {
            // Under [P, x, y]: P=Bound 2, x=Bound 1, y=Bound 0.
            let conj_c = cst("HOL.conj", ty_fun(ty_bool(), ty_fun(ty_bool(), ty_bool())));
            let py = app(bnd(2), bnd(0));
            let eqyx = heq(alpha, bnd(0), bnd(1));
            let forall_y = all(alpha.clone(), imp(py, eqyx));
            let px = app(bnd(1), bnd(0)); // under [P, x]: P=Bound 1, x=Bound 0
            let conj = app(app(conj_c, px), forall_y);
            let ex_c = cst(
                "HOL.Ex",
                ty_fun(ty_fun(alpha.clone(), ty_bool()), ty_bool()),
            );
            let ex_body = app(ex_c, abs(alpha.clone(), conj));
            Some(abs(pred_ty, ex_body))
        }
        // λs f. f s   (Let)
        "HOL.Let" => None, // reconstructed specially (needs β), see raw_def_prop
        // λP. ∀x. P x
        "HOL.induct_forall" => {
            let px = app(bnd(1), bnd(0)); // under [P, x]: P=Bound 1
            Some(abs(pred_ty, all(alpha.clone(), px)))
        }
        // λx y. x = y
        "HOL.induct_equal" => {
            let body = heq(alpha, bnd(1), bnd(0));
            Some(abs(alpha.clone(), abs(alpha.clone(), body)))
        }
        // λpat val. True   (NO_MATCH) — reconstructed specially (needs β), see
        // raw_def_prop.
        "HOL.NO_MATCH" => None,
        // --- the `HOL.ATP` first-order aliases (round-9) ---
        // fFalse ≡ False ; fTrue ≡ True   (bare-constant RHS)
        "ATP.fFalse" => Some(cst("HOL.False", ty_bool())),
        "ATP.fTrue" => Some(cst("HOL.True", ty_bool())),
        // fNot ≡ λP. ¬ P
        "ATP.fNot" => {
            let not_c = cst("HOL.Not", ty_fun(ty_bool(), ty_bool()));
            Some(abs(ty_bool(), app(not_c, bnd(0))))
        }
        // fconj ≡ λP Q. P ∧ Q ; fdisj ≡ λP Q. P ∨ Q ; fimplies ≡ λP Q. P ⟶ Q
        "ATP.fconj" | "ATP.fdisj" | "ATP.fimplies" => {
            let head = match name {
                "ATP.fconj" => "HOL.conj",
                "ATP.fdisj" => "HOL.disj",
                _ => "HOL.implies",
            };
            let c = cst(head, ty_fun(ty_bool(), ty_fun(ty_bool(), ty_bool())));
            Some(abs(ty_bool(), abs(ty_bool(), app(app(c, bnd(1)), bnd(0)))))
        }
        // fAll ≡ λP. All P ; fEx ≡ λP. Ex P   (bare predicate application)
        "ATP.fAll" | "ATP.fEx" => {
            let head = if name == "ATP.fAll" {
                "HOL.All"
            } else {
                "HOL.Ex"
            };
            let c = cst(head, ty_fun(pred_ty.clone(), ty_bool()));
            Some(abs(pred_ty, app(c, bnd(0))))
        }
        // fequal ≡ λx y. x = y
        "ATP.fequal" => {
            let body = heq(alpha, bnd(1), bnd(0));
            Some(abs(alpha.clone(), abs(alpha.clone(), body)))
        }
        // fComp ≡ λP x. ¬ P x
        "ATP.fComp" => {
            let not_c = cst("HOL.Not", ty_fun(ty_bool(), ty_bool()));
            let body = app(not_c, app(bnd(1), bnd(0)));
            Some(abs(pred_ty, abs(alpha.clone(), body)))
        }
        // fChoice ≡ Eps   (bare-constant RHS)
        "ATP.fChoice" => Some(cst(
            "Hilbert_Choice.Eps",
            ty_fun(ty_fun(alpha.clone(), ty_bool()), alpha.clone()),
        )),
        _ => None,
    }
}

/// Reconstruct the full point-free `…_def_raw` equation `Pure.eq C (λargs. body)`
/// as an `IsaTerm`, from the object type(s) supplied by a leaf reference's
/// `tyinst`. `alpha` is the primary object type `'a`; `beta` is the secondary
/// (`Let`'s value type / `NO_MATCH`'s second arg type), defaulting to `'a` when the
/// leaf only carries one. Returns `None` for `HOL.If` (needs `HOL.The`).
pub(crate) fn raw_def_prop(name: &str, alpha: &IsaType, beta: &IsaType) -> Option<IsaTerm> {
    // Build the LHS bare constant at its full type and the RHS body, then assemble
    // `Pure.eq C rhs` at the constant's result type.
    let (const_ty, rhs, eq_ty) = match name {
        "HOL.Let" => {
            // Let : α ⇒ (α⇒β) ⇒ β ; body λs f. f s ; eq at (α⇒(α⇒β)⇒β).
            let fn_ty = ty_fun(alpha.clone(), beta.clone());
            let cty = ty_fun(alpha.clone(), ty_fun(fn_ty.clone(), beta.clone()));
            // λs f. f s  — under [s, f]: s=Bound 1, f=Bound 0.
            let body = abs(alpha.clone(), abs(fn_ty, app(bnd(0), bnd(1))));
            (cty, body, cty_of_let(alpha, beta))
        }
        "HOL.NO_MATCH" => {
            // NO_MATCH : α ⇒ β ⇒ bool ; body λpat val. True.
            let cty = ty_fun(alpha.clone(), ty_fun(beta.clone(), ty_bool()));
            let body = abs(alpha.clone(), abs(beta.clone(), cst("HOL.True", ty_bool())));
            (cty.clone(), body, cty)
        }
        _ => {
            let rhs = raw_def_rhs(name, alpha)?;
            // The constant's own type = the RHS body's function type. Recover it from
            // the argument/result shape per name (all logical ones are predicate or
            // binary-relation shaped).
            let cty = pointfree_const_hol_type(name, alpha)?;
            (cty.clone(), rhs, cty)
        }
    };
    let c = cst(name, const_ty);
    let eq_c = cst("Pure.eq", ty_fun(eq_ty.clone(), ty_fun(eq_ty, ty_bool())));
    Some(app(app(eq_c, c), rhs))
}

/// The HOL type of a unary/relation point-free constant at object type `alpha`.
fn pointfree_const_hol_type(name: &str, alpha: &IsaType) -> Option<IsaType> {
    let pred_ty = ty_fun(alpha.clone(), ty_bool());
    match name {
        "HOL.All" | "HOL.Ex" | "HOL.Uniq" | "HOL.Ex1" | "HOL.induct_forall" | "ATP.fAll"
        | "ATP.fEx" => Some(ty_fun(pred_ty, ty_bool())),
        "HOL.induct_equal" | "ATP.fequal" => {
            Some(ty_fun(alpha.clone(), ty_fun(alpha.clone(), ty_bool())))
        }
        "ATP.fFalse" | "ATP.fTrue" => Some(ty_bool()),
        "ATP.fNot" => Some(ty_fun(ty_bool(), ty_bool())),
        "ATP.fconj" | "ATP.fdisj" | "ATP.fimplies" => {
            Some(ty_fun(ty_bool(), ty_fun(ty_bool(), ty_bool())))
        }
        "ATP.fComp" => Some(ty_fun(pred_ty, ty_fun(alpha.clone(), ty_bool()))),
        "ATP.fChoice" => Some(ty_fun(pred_ty, alpha.clone())),
        _ => None,
    }
}

/// `Let`'s constant/eq type `α ⇒ (α⇒β) ⇒ β`.
fn cty_of_let(alpha: &IsaType, beta: &IsaType) -> IsaType {
    let fn_ty = ty_fun(alpha.clone(), beta.clone());
    ty_fun(alpha.clone(), ty_fun(fn_ty, beta.clone()))
}

impl Ctx {
    /// Prove a point-free `…_def_raw` axiom referenced as a **leaf** (`bootstrap.rs`
    /// `axm` node), from the object type(s) the leaf's `tyinst` supplies. Wraps the
    /// reconstructed equation ([`raw_def_prop`]) as a synthetic `IsaProvenTheorem`
    /// and reuses [`Self::prove_pointfree_def_raw`], returning the proof term
    /// (dropping the synthetic statement type — the enclosing consumer re-checks it).
    /// Returns `None` for a name it does not reconstruct (e.g. `HOL.If`).
    pub(crate) fn prove_pointfree_def_raw_leaf(
        &mut self,
        name: &str,
        alpha: &IsaType,
        beta: &IsaType,
        binders: &mut Vec<Binder>,
    ) -> Result<Option<Expr>, TranslateError> {
        // Leaf names are the raw axiom names (`HOL.All_def_raw`, …); strip the
        // `_def_raw` suffix to recover the bare constant name (`HOL.All`).
        let base = name.strip_suffix("_def_raw").unwrap_or(name);
        let Some(prop) = raw_def_prop(base, alpha, beta) else {
            return Ok(None);
        };
        let thm = IsaProvenTheorem {
            name: String::new(),
            serial: 0,
            prop,
            proof: super::super::super::isabelle_pure::IsaProof::Min,
        };
        match self.prove_pointfree_def_raw(&thm, binders)? {
            Some((_ty, proof)) => Ok(Some(proof)),
            None => Ok(None),
        }
    }
}

/// Prove `@Eq ((α→Prop)→Prop) (λP. ∀x. P x) (λP. P = (λx. True))` — the point-free
/// `All_def` — by `funext` over the pointwise [`all_def_bridge_proof`].
///
/// `lhs_sem`/`rhs` are the already-embedded `λP. …` operands (used verbatim as the
/// `funext` operands so the proof's inferred type is bit-identical to the stored
/// equation). `arg_tys` is the single-element `[α ⇒ bool]` predicate type, from
/// which the object domain `α` is recovered.
fn all_def_pointfree_bridge(
    ctx: &mut Ctx,
    arg_tys: &[IsaType],
    lhs_sem: &Expr,
    rhs: &Expr,
) -> Result<Expr, TranslateError> {
    // The single argument type is the predicate type `α ⇒ bool`; α is its domain.
    let pred_ty = arg_tys
        .first()
        .ok_or(TranslateError::Unsupported("All_def_raw: no predicate arg"))?;
    let dom_ty = eq_operand_type(pred_ty).ok_or(TranslateError::Unsupported(
        "All_def_raw: predicate not a function",
    ))?;
    let alpha = ctx.embed_type(dom_ty)?;
    let pred = Expr::arrow(alpha.clone(), Expr::prop());
    // funext over `P : α → Prop`: at each `P` (a fresh fvar), the pointwise proof is
    // `all_def_bridge_proof(α, P)`, which proves `@Eq Prop (∀x. P x) (P = λx.True)`.
    // `lhs_sem P` β-reduces to `∀x. P x` and `rhs P` to `P = λx.True`, so the
    // pointwise types line up with `funext`'s family `λP. @Eq Prop (lhs_sem P) (rhs P)`.
    const FP: u64 = 0xA11D_0100;
    let p = Expr::fvar(FVarId::new(FP));
    let pointwise_body = all_def_bridge_proof(&alpha, &p);
    let pointwise = Expr::lam(
        BinderInfo::Default,
        pred.clone(),
        pointwise_body.abstract_fvar(FVarId::new(FP)),
    );
    // The codomain family for funext: `β = λ(_:α→Prop). Prop` — both operands are
    // `Prop`-valued, so `funext`'s target equation is at `(α→Prop) → Prop`.
    let beta = Expr::lam(BinderInfo::Default, pred.clone(), Expr::prop());
    Ok(Expr::apps(
        Expr::const_str_levels("funext", vec![obj_level(), obj_level()]),
        [pred, beta, lhs_sem.clone(), rhs.clone(), pointwise],
    ))
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definition body for `NNVerify.Zonotope.contains`.
//!
//! Split from `nn_verify_zonotope.rs` (#3556) so the containment predicate's
//! reducible body can live as `Declaration::Definition` with a kernel-checkable
//! existential body — not `Declaration::Axiom` — while keeping each file and
//! function within the repository's code-quality bounds (500 lines per file,
//! 80 lines per function).
//!
//! ## Body unfolding
//!
//! ```text
//! NNVerify.Zonotope.contains {n k} z x :=
//!   ∃ ε : NNVec k,
//!     (∀ i : Fin k, (-1 : Rat) ≤ ε i ∧ ε i ≤ 1) ∧
//!     x = NNVec.add z.center (NNMat.mulVec z.generators ε)
//! ```
//!
//! Rationale: see `designs/2026-04-19-foundational-axiom-whitelist-expansion.md`
//! Category 3 / FU-6. Registering `contains` as a bare axiom laundered
//! interface content into foundational status.

use super::nn_verify_zonotope::ZonotopeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// Register `NNVerify.Zonotope.contains` as a reducible `Declaration::Definition`.
    ///
    /// Type: `{n k : Nat} -> Zonotope n k -> NNVec n -> Prop`.
    ///
    /// Value (see module doc for unfolding):
    ///   `fun {n k} z x => Exists (α := NNVec k) (fun ε => And bounds eq_x)`.
    pub(super) fn register_zonotope_contains(
        &mut self,
        c: &ZonotopeConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.Zonotope.contains"))
            .is_some()
        {
            return Ok(());
        }
        let ty = build_contains_type(c);
        let value = build_contains_value(c);
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.Zonotope.contains"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

/// Build the declaration type:
///   `{n k : Nat} -> Zonotope n k -> NNVec n -> Prop`.
fn build_contains_type(c: &ZonotopeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let vec_n = c.vec_of(n);
    let (z_id, _) = b.fresh_local(zono_nk.clone());
    let (x_id, _) = b.fresh_local(vec_n.clone());
    let r = b.mk_pi(x_id, BinderInfo::Default, vec_n, c.prop.clone());
    let r = b.mk_pi(z_id, BinderInfo::Default, zono_nk, r);
    let r = b.mk_pi(k_id, BinderInfo::Implicit, c.nat.clone(), r);
    let r = b.mk_pi(n_id, BinderInfo::Implicit, c.nat.clone(), r);
    b.finish(r)
}

/// Build the reducible body:
///
/// ```text
/// fun {n k : Nat} (z : Zonotope n k) (x : NNVec n) =>
///   Exists.{1} (NNVec k) (fun (ε : NNVec k) =>
///     And
///       (∀ i : Fin k, ((-1 : Rat) ≤ ε i) ∧ (ε i ≤ 1))
///       (x = NNVec.add n z.center (NNMat.mulVec n k z.generators ε)))
/// ```
fn build_contains_value(c: &ZonotopeConsts) -> Expr {
    let neg_one = Expr::app(c.rat_neg.clone(), c.rat_one.clone());
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let vec_n = c.vec_of(n.clone());
    let vec_k = c.vec_of(k.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());
    let (x_id, x) = b.fresh_local(vec_n.clone());

    // z.center : NNVec n
    let center = Expr::proj(Name::from_string("NNVerify.Zonotope"), 0, z.clone());
    // z.generators : NNMat n k
    let generators = Expr::proj(Name::from_string("NNVerify.Zonotope"), 1, z);

    let body_lam = build_contains_body_lam(
        c, &b, &n, &k, &neg_one, &vec_n, &vec_k, &x, center, generators,
    );

    // `NNVec k : Type 0 = Sort 1`, so we use `Exists.{1}` (`exists_type0`).
    let exists_expr = Expr::app(Expr::app(c.exists_type0.clone(), vec_k), body_lam);

    let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, exists_expr);
    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, e);
    let e = b.mk_lam(k_id, BinderInfo::Implicit, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Implicit, c.nat.clone(), e);
    b.finish(e)
}

/// Build `fun (ε : NNVec k) => And bounds eq_x` using a `child_of` builder so
/// `ε`'s local-id namespace is fresh.
fn build_contains_body_lam(
    c: &ZonotopeConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    neg_one: &Expr,
    vec_n: &Expr,
    vec_k: &Expr,
    x: &Expr,
    center: Expr,
    generators: Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = ch.fresh_local(vec_k.clone());

    let fin_k = Expr::app(c.fin.clone(), k.clone());
    let bounds = build_bounds_forall(c, &ch, &fin_k, &eps, neg_one);

    // rhs : NNVec.add n z.center (NNMat.mulVec n k z.generators ε).
    // NNVec.add has implicit `{n}`; NNMat.mulVec has implicit `{m} {n}`.
    // Implicit args are passed explicitly when building `Expr` applications.
    let mul = Expr::apps(
        c.nn_mat_mul_vec.clone(),
        [n.clone(), k.clone(), generators, eps.clone()],
    );
    let rhs = Expr::apps(c.nn_vec_add.clone(), [n.clone(), center, mul]);
    let eq_x = c.eq_of(vec_n.clone(), x.clone(), rhs);

    let conj_body = Expr::app(Expr::app(c.and.clone(), bounds), eq_x);
    let lam = ch.mk_lam(eps_id, BinderInfo::Default, vec_k.clone(), conj_body);
    ch.finish_child(lam)
}

/// Build `∀ i : Fin k, (-1 ≤ ε i) ∧ (ε i ≤ 1)` as a Π-expression.
fn build_bounds_forall(
    c: &ZonotopeConsts,
    parent: &EnvDeclBuilder,
    fin_k: &Expr,
    eps: &Expr,
    neg_one: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = ch.fresh_local(fin_k.clone());
    let eps_i = Expr::app(eps.clone(), i);
    let conj = Expr::app(
        Expr::app(c.and.clone(), c.rat_le(neg_one.clone(), eps_i.clone())),
        c.rat_le(eps_i, c.rat_one.clone()),
    );
    let r = ch.mk_pi(i_id, BinderInfo::Default, fin_k.clone(), conj);
    ch.finish_child(r)
}

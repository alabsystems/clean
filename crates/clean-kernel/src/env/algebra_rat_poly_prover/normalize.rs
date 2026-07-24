// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `normalize` — structural recursion turning an `Expr` into its canonical
//! polynomial form, emitting the proof `e = canon` as a by-product.

use super::{NormResult, Poly, PolyProveError, RatPolyProver};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;

impl RatPolyProver {
    /// Normalize `e` to canonical form with a proof `e = canon`.
    pub(crate) fn normalize(
        &self,
        parent: &EnvDeclBuilder,
        e: &Expr,
    ) -> Result<NormResult, PolyProveError> {
        // Atoms and constants are already canonical (their own reify).
        if let Some(idx) = self.var_index(e) {
            let poly = Poly::var(idx);
            let canon = self.reify_poly(&poly);
            // canon is exactly `e` (single var, coeff 1) → refl on e.
            let proof = self.refl(e.clone());
            return Ok(NormResult { poly, canon, proof });
        }
        match e.kind() {
            ExprKind::Const(name, _) if name == &Name::from_string("Rat.one") => {
                let poly = Poly::one();
                let canon = self.reify_poly(&poly);
                Ok(NormResult {
                    poly,
                    canon,
                    proof: self.refl(e.clone()),
                })
            }
            ExprKind::Const(name, _) if name == &Name::from_string("Rat.zero") => {
                let poly = Poly::zero();
                let canon = self.reify_poly(&poly);
                Ok(NormResult {
                    poly,
                    canon,
                    proof: self.refl(e.clone()),
                })
            }
            _ => self.normalize_app(parent, e),
        }
    }

    fn normalize_app(
        &self,
        parent: &EnvDeclBuilder,
        e: &Expr,
    ) -> Result<NormResult, PolyProveError> {
        let (head, args) = super::uncurry(e);
        let name = match head.kind() {
            ExprKind::Const(n, _) => n.to_string(),
            _ => return Err(PolyProveError::UnrecognizedExpr(format!("{:?}", e.kind()))),
        };
        match (name.as_str(), args.len()) {
            ("Rat.add", 2) => self.normalize_add(parent, e, &args[0], &args[1]),
            ("Rat.mul", 2) => self.normalize_mul(parent, e, &args[0], &args[1]),
            ("Rat.neg", 1) => self.normalize_neg(parent, e, &args[0]),
            ("Rat.sub", 2) => {
                // a − b  ≡  a + (−b). Prove e = a + (−b) (definitional via refl is
                // unsafe across whnf; instead rewrite explicitly is unnecessary —
                // Rat.sub is reducible to add∘neg, so the kernel accepts a proof of
                // `a + (−b) = canon` as a proof of `e = canon` only up to defeq. To
                // stay robust we build the proof against the `add (neg ...)` form
                // and rely on definitional unfolding of `Rat.sub`.)
                let neg_b = self.neg(args[1].clone());
                let as_add = self.add(args[0].clone(), neg_b);
                let inner = self.normalize_app(parent, &as_add)?;
                // proof: e = canon, where e ≡ Rat.sub a b is defeq to as_add.
                // Use Eq.trans (refl-cast) — the kernel checks `e = canon` because
                // `e` and `as_add` are definitionally equal, so `inner.proof`
                // (typed `as_add = canon`) also has type `e = canon` after whnf.
                Ok(NormResult {
                    poly: inner.poly,
                    canon: inner.canon,
                    proof: inner.proof,
                })
            }
            _ => Err(PolyProveError::UnrecognizedExpr(format!(
                "head {name} with {} args",
                args.len()
            ))),
        }
    }

    fn normalize_add(
        &self,
        parent: &EnvDeclBuilder,
        e: &Expr,
        a: &Expr,
        b: &Expr,
    ) -> Result<NormResult, PolyProveError> {
        let na = self.normalize(parent, a)?;
        let nb = self.normalize(parent, b)?;
        // Step 1: e = add A B   (congr both sides)
        let add_c = self.add_const();
        // (a + b) = (A + b)
        let a_plus_b_to_aa = self.cong_left(
            parent,
            &add_c,
            a.clone(),
            na.canon.clone(),
            b.clone(),
            na.proof,
        );
        let aa_plus_b = self.add(na.canon.clone(), b.clone());
        // (A + b) = (A + B)
        let to_ab = self.cong_right(
            parent,
            &add_c,
            b.clone(),
            nb.canon.clone(),
            na.canon.clone(),
            nb.proof,
        );
        let add_ab = self.add(na.canon.clone(), nb.canon.clone());
        let e1 = self.trans(e.clone(), aa_plus_b, add_ab.clone(), a_plus_b_to_aa, to_ab);
        // Step 2: add A B = reify(merge)
        let merged = na.poly.add(&nb.poly);
        let canon = self.reify_poly(&merged);
        let h2 = self.prove_add_of_canon(parent, &na.poly, &nb.poly);
        let proof = self.trans(e.clone(), add_ab, canon.clone(), e1, h2);
        Ok(NormResult {
            poly: merged,
            canon,
            proof,
        })
    }

    fn normalize_mul(
        &self,
        parent: &EnvDeclBuilder,
        e: &Expr,
        a: &Expr,
        b: &Expr,
    ) -> Result<NormResult, PolyProveError> {
        let na = self.normalize(parent, a)?;
        let nb = self.normalize(parent, b)?;
        let mul_c = self.mul_const();
        // (a · b) = (A · b)
        let a_to_aa = self.cong_left(
            parent,
            &mul_c,
            a.clone(),
            na.canon.clone(),
            b.clone(),
            na.proof,
        );
        let aa_b = self.mul(na.canon.clone(), b.clone());
        // (A · b) = (A · B)
        let to_ab = self.cong_right(
            parent,
            &mul_c,
            b.clone(),
            nb.canon.clone(),
            na.canon.clone(),
            nb.proof,
        );
        let mul_ab = self.mul(na.canon.clone(), nb.canon.clone());
        let e1 = self.trans(e.clone(), aa_b, mul_ab.clone(), a_to_aa, to_ab);
        // (A · B) = reify(convolve)
        let prod = na.poly.mul(&nb.poly);
        let canon = self.reify_poly(&prod);
        let h2 = self.prove_mul_of_canon(parent, &na.poly, &nb.poly);
        let proof = self.trans(e.clone(), mul_ab, canon.clone(), e1, h2);
        Ok(NormResult {
            poly: prod,
            canon,
            proof,
        })
    }

    fn normalize_neg(
        &self,
        parent: &EnvDeclBuilder,
        e: &Expr,
        a: &Expr,
    ) -> Result<NormResult, PolyProveError> {
        let na = self.normalize(parent, a)?;
        // e = neg A   (congrArg neg)
        let cong = self.cong_neg(parent, a.clone(), na.canon.clone(), na.proof);
        let neg_a = self.neg(na.canon.clone());
        let negated = na.poly.neg();
        let canon = self.reify_poly(&negated);
        let h2 = self.prove_neg_of_canon(parent, &na.poly);
        let proof = self.trans(e.clone(), neg_a, canon.clone(), cong, h2);
        Ok(NormResult {
            poly: negated,
            canon,
            proof,
        })
    }
}

// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Actual UInt AND source definitions reduce through ofNat and its modulus.
//! The two carrier bounds derive the AND bound, so mod_eq_of_lt removes it.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

const WIDTHS: [(&str, u64); 4] = [("UInt8", 8), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)];

fn k(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn build_uint_tonat_land(ty_name: &str, width: u64) -> (Expr, Expr) {
    let ty = k(ty_name);
    let to_nat = k(&format!("{ty_name}.toNat"));
    let mut scope = EnvDeclBuilder::new();
    let (a_id, a) = scope.fresh_local(ty.clone());
    let (b_id, b) = scope.fresh_local(ty.clone());
    let a_nat = Expr::app(to_nat.clone(), a.clone());
    let b_nat = Expr::app(to_nat.clone(), b.clone());
    let result = Expr::apps(k("Nat.land"), [a_nat.clone(), b_nat.clone()]);
    let actual = Expr::app(
        to_nat,
        Expr::apps(k(&format!("{ty_name}.land")), [a.clone(), b.clone()]),
    );
    let claim = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [k("Nat"), actual, result.clone()],
    );
    let bound = Expr::apps(
        k("Nat.land_lt_two_pow"),
        [
            Expr::nat_lit(width),
            a_nat,
            b_nat,
            Expr::app(k(&format!("{ty_name}.toNat_lt")), a),
            Expr::app(k(&format!("{ty_name}.toNat_lt")), b),
        ],
    );
    let proof = Expr::apps(
        k("Nat.mod_eq_of_lt"),
        [result, k(&format!("{ty_name}.size")), bound],
    );
    let claim = scope.mk_pi(b_id, BinderInfo::Default, ty.clone(), claim);
    let claim = scope.mk_pi(a_id, BinderInfo::Default, ty.clone(), claim);
    let proof = scope.mk_lam(b_id, BinderInfo::Default, ty.clone(), proof);
    let proof = scope.mk_lam(a_id, BinderInfo::Default, ty, proof);
    (scope.finish(claim), scope.finish(proof))
}

impl Environment {
    pub(crate) fn register_uint_land_tonat_proofs(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.register_nat_land_bound_proof()?;
        self.init_uint_floor_tonat_lemmas()?;
        for (ty_name, width) in WIDTHS {
            let (type_, value) = build_uint_tonat_land(ty_name, width);
            self.ensure_exact_checked_decl(Declaration::Theorem {
                name: Name::from_string(&format!("{ty_name}.toNat_land")),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "uint_land_tonat_proofs_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Actual UInt right shifts decode to division by the masked power of two.
//! The quotient bound removes only the redundant finite-carrier result wrap.
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

const WIDTHS: [(&str, u64); 4] = [("UInt8", 8), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)];
fn k(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(k(name), args)
}
fn build_uint_tonat_shiftright(ty_name: &str, width: u64) -> (Expr, Expr) {
    let ty = k(ty_name);
    let to_nat = k(&format!("{ty_name}.toNat"));
    let mut scope = EnvDeclBuilder::new();
    let (a_id, a) = scope.fresh_local(ty.clone());
    let (b_id, b) = scope.fresh_local(ty.clone());
    let a_nat = Expr::app(to_nat.clone(), a.clone());
    let amount = app(
        "Nat.mod",
        [Expr::app(to_nat.clone(), b.clone()), Expr::nat_lit(width)],
    );
    let divisor = app("Nat.pow", [Expr::nat_lit(2), amount]);
    let quotient = app("Nat.div", [a_nat.clone(), divisor.clone()]);
    let actual = Expr::app(
        to_nat,
        app(&format!("{ty_name}.shiftRight"), [a.clone(), b]),
    );
    let claim = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [k("Nat"), actual, quotient.clone()],
    );
    let size = k(&format!("{ty_name}.size"));
    let bound = app(
        "Nat.lt_of_le_of_lt",
        [
            quotient.clone(),
            a_nat.clone(),
            size.clone(),
            app("Nat.div_le_self", [a_nat, divisor]),
            Expr::app(k(&format!("{ty_name}.toNat_lt")), a),
        ],
    );
    let proof = app("Nat.mod_eq_of_lt", [quotient, size, bound]);
    let claim = scope.mk_pi(b_id, BinderInfo::Default, ty.clone(), claim);
    let claim = scope.mk_pi(a_id, BinderInfo::Default, ty.clone(), claim);
    let proof = scope.mk_lam(b_id, BinderInfo::Default, ty.clone(), proof);
    let proof = scope.mk_lam(a_id, BinderInfo::Default, ty, proof);
    (scope.finish(claim), scope.finish(proof))
}
impl Environment {
    pub(crate) fn register_uint_shiftright_tonat_proofs(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_uint_floor_tonat_lemmas()?;
        for (ty_name, width) in WIDTHS {
            let (type_, value) = build_uint_tonat_shiftright(ty_name, width);
            self.ensure_exact_checked_decl(Declaration::Theorem {
                name: Name::from_string(&format!("{ty_name}.toNat_shiftRight")),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        Ok(())
    }
}
#[cfg(test)]
#[path = "uint_shiftright_tonat_proofs_tests.rs"]
mod tests;

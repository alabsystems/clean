// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Actual UInt left shifts decode to multiplication by the masked power of two.
//! The finite-carrier modulus remains explicit in the source statement.
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

#[path = "uint_shiftleft_tonat_induction.rs"]
mod induction;

const WIDTHS: [(&str, u64); 4] = [("UInt8", 8), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)];
fn k(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(k(name), args)
}
fn build_uint_tonat_shiftleft(ty_name: &str, width: u64) -> (Expr, Expr) {
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
    let factor = app("Nat.pow", [Expr::nat_lit(2), amount.clone()]);
    let residue = app(
        "Nat.mod",
        [
            app("Nat.mul", [a_nat.clone(), factor.clone()]),
            k(&format!("{ty_name}.size")),
        ],
    );
    let actual = Expr::app(to_nat, app(&format!("{ty_name}.shiftLeft"), [a.clone(), b]));
    let claim = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [k("Nat"), actual, residue.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ),
        [
            k("Nat"),
            k("Nat"),
            app("Nat.shiftLeft", [a_nat.clone(), amount.clone()]),
            app("Nat.mul", [a_nat.clone(), factor]),
            Expr::lam(
                BinderInfo::Default,
                k("Nat"),
                app("Nat.mod", [Expr::bvar(0), k(&format!("{ty_name}.size"))]),
            ),
            app("Nat.shiftLeft_eq", [a_nat, amount]),
        ],
    );
    let claim = scope.mk_pi(b_id, BinderInfo::Default, ty.clone(), claim);
    let claim = scope.mk_pi(a_id, BinderInfo::Default, ty.clone(), claim);
    let proof = scope.mk_lam(b_id, BinderInfo::Default, ty.clone(), proof);
    let proof = scope.mk_lam(a_id, BinderInfo::Default, ty, proof);
    (scope.finish(claim), scope.finish(proof))
}
impl Environment {
    pub(crate) fn register_uint_shiftleft_tonat_proofs(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_uint_floor_tonat_lemmas()?;
        self.register_nat_mul_one_proof()?;
        self.register_nat_mul_assoc_proof()?;
        self.ensure_exact_checked_decl(induction::declaration())?;
        for (ty_name, width) in WIDTHS {
            let (type_, value) = build_uint_tonat_shiftleft(ty_name, width);
            self.ensure_exact_checked_decl(Declaration::Theorem {
                name: Name::from_string(&format!("{ty_name}.toNat_shiftLeft")),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        Ok(())
    }
}
#[cfg(test)]
#[path = "uint_shiftleft_tonat_proofs_tests.rs"]
mod tests;

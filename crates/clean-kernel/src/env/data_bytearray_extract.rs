// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Half-open byte slices over the ordinary source prelude's List-backed Array.
//! Import mode leaves the genuine Init declaration to the checked importer.

use super::monad_term::{cst, Tele};
use super::{Declaration, EnvError, Environment};
use crate::{Expr, Level, Name};

fn extract_decl() -> Declaration {
    let zero = [Level::zero()];
    let byte = cst("UInt8", &[]);
    let bytes = cst("ByteArray", &[]);
    let nat = cst("Nat", &[]);
    let mut t = Tele::new();
    let a = t.arg(bytes.clone());
    let start = t.arg(nat.clone());
    let end = t.arg(nat);
    let data = Expr::app(cst("ByteArray.data", &[]), a);
    let list = Expr::apps(cst("Array.toList", &zero), [byte.clone(), data]);
    let dropped = Expr::apps(cst("List.drop", &zero), [byte.clone(), start.clone(), list]);
    let count = Expr::apps(cst("Nat.sub", &[]), [end, start]);
    let slice = Expr::apps(cst("List.take", &zero), [byte.clone(), count, dropped]);
    let array = Expr::apps(cst("Array.mk", &zero), [byte, slice]);
    let value = t.lam(Expr::app(cst("ByteArray.mk", &[]), array));
    Declaration::Definition {
        name: Name::from_string("ByteArray.extract"),
        level_params: vec![],
        type_: t.pi(bytes),
        value,
        is_reducible: true,
    }
}

impl Environment {
    pub(crate) fn register_bytearray_extract(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_byte_array()?;
        self.ensure_exact_checked_decl(extract_decl())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_extract_is_checked_axiom_free_and_idempotent() {
        let mut env = Environment::try_with_prelude().expect("checked source prelude");
        let name = Name::from_string("ByteArray.extract");
        let info = env.get_const(&name).expect("source slice definition");
        assert!(info.value.is_some());
        assert!(info.level_params.is_empty());
        assert!(env.axiom_deps(&name).expect("slice closure").is_empty());
        let before = (env.num_constants(), env.num_instances());
        env.register_bytearray_extract()
            .expect("exact registration");
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }

    #[test]
    fn source_extract_preserves_import_ownership() {
        let mut env = Environment::try_with_prelude_for_import().expect("checked import prelude");
        env.register_bytearray_extract()
            .expect("import suppression");
        assert!(env
            .get_const(&Name::from_string("ByteArray.extract"))
            .is_none());
    }
}

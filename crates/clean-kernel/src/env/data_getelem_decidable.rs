// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked Nat indexing for ByteArray and Lean's low-priority optional lookup.
//! Ordinary source elaboration uses the existing checked Array accessor for
//! the ByteArray field. Import mode loads the original Lean declarations.

use crate::env::monad_term::{cst, lparam, type_at, Tele};
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

const BOUNDED_BYTE_INDEX: &str = "ByteArray.instGetElemNatUInt8LtSize";
const DECIDABLE_INDEX: &str = "instGetElem?OfGetElemOfDecidable";

impl Environment {
    pub(crate) fn init_bytearray_and_decidable_indexing(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_option_ops()?;
        self.register_bounded_byte_index()?;
        self.register_decidable_index()
    }

    fn register_bounded_byte_index(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string(BOUNDED_BYTE_INDEX);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = Level::zero();
        let levels = [zero.clone(), zero.clone(), zero.clone()];
        let nat = cst("Nat", &[]);
        let byte = cst("UInt8", &[]);
        let bytes = cst("ByteArray", &[]);
        let arr = Expr::app(cst("Array", std::slice::from_ref(&zero)), byte.clone());
        let array_size = Expr::app(cst("Array.size", std::slice::from_ref(&zero)), byte.clone());
        let array_instance = Expr::app(
            cst("Array.instGetElemNatLtSize", std::slice::from_ref(&zero)),
            byte.clone(),
        );
        let lt = Expr::apps(
            cst("LT.lt", std::slice::from_ref(&zero)),
            [nat.clone(), cst("instLTNat", &[])],
        );
        let valid = |carrier: &Expr, size: Expr| {
            let mut t = Tele::new();
            let collection = t.arg(carrier.clone());
            let index = t.arg(nat.clone());
            t.lam(Expr::apps(lt.clone(), [index, Expr::app(size, collection)]))
        };
        let byte_valid = valid(&bytes, cst("ByteArray.size", &[]));
        let array_valid = valid(&arr, array_size);
        let mut field = Tele::new();
        let collection = field.arg(bytes.clone());
        let index = field.arg(nat.clone());
        let bound = field.arg(Expr::apps(
            byte_valid.clone(),
            [collection.clone(), index.clone()],
        ));
        let data = Expr::app(cst("ByteArray.data", &[]), collection);
        let getter = field.lam(Expr::apps(
            cst("GetElem.getElem", &levels),
            [
                arr,
                nat.clone(),
                byte.clone(),
                array_valid,
                array_instance,
                data,
                index,
                bound,
            ],
        ));
        let args = [bytes, nat, byte, byte_valid];
        let type_ = Expr::apps(cst("GetElem", &levels), args.clone());
        let value = Expr::app(Expr::apps(cst("GetElem.mk", &levels), args), getter);
        self.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name,
            class_name: Name::from_string("GetElem"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Init/GetElem.lean derives GetElem? from GetElem and decidable bounds.
    /// The inherited bang field uses Option.getD with the caller's default.
    fn register_decidable_index(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string(DECIDABLE_INDEX);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let levels = [lparam("u_1"), lparam("u_2"), lparam("u_3")];
        let elem_level = std::slice::from_ref(&levels[2]);
        let sort_elem = Level::succ(levels[2].clone());
        let mut t = Tele::new();
        let coll = t.imp(type_at(&levels[0]));
        let idx = t.imp(type_at(&levels[1]));
        let elem = t.imp(type_at(&levels[2]));
        let valid = t.imp(Expr::arrow(
            coll.clone(),
            Expr::arrow(idx.clone(), Expr::sort(Level::zero())),
        ));
        let args = [coll.clone(), idx.clone(), elem.clone(), valid.clone()];
        let parent = t.inst(Expr::apps(cst("GetElem", &levels), args.clone()));
        let decision = {
            let mut bounds = Tele::child(&t);
            let xs = bounds.arg(coll.clone());
            let i = bounds.arg(idx.clone());
            let predicate = Expr::apps(valid.clone(), [xs, i]);
            t.inst(bounds.pi(Expr::app(cst("Decidable", &[]), predicate)))
        };
        let optional = {
            let mut getter = Tele::child(&t);
            let xs = getter.arg(coll.clone());
            let i = getter.arg(idx.clone());
            let predicate = Expr::apps(valid.clone(), [xs.clone(), i.clone()]);
            let decide = Expr::apps(decision, [xs.clone(), i.clone()]);
            let mut yes = Tele::child(&getter);
            let bound = yes.arg(predicate.clone());
            let get = Expr::apps(
                Expr::apps(cst("GetElem.getElem", &levels), args.clone()),
                [parent.clone(), xs, i, bound],
            );
            let some = yes.lam(Expr::apps(
                cst("Option.some", elem_level),
                [elem.clone(), get],
            ));
            let mut no = Tele::child(&getter);
            let _ = no.arg(Expr::app(cst("Not", &[]), predicate.clone()));
            let none = no.lam(Expr::app(cst("Option.none", elem_level), elem.clone()));
            let opt = Expr::app(cst("Option", elem_level), elem.clone());
            getter.lam(Expr::apps(
                cst("dite", std::slice::from_ref(&sort_elem)),
                [opt, predicate, decide, some, none],
            ))
        };
        let bang = {
            let mut getter = Tele::child(&t);
            let inhabited = getter.inst(Expr::app(
                cst("Inhabited", std::slice::from_ref(&sort_elem)),
                elem.clone(),
            ));
            let xs = getter.arg(coll);
            let i = getter.arg(idx);
            let default = Expr::apps(
                cst("Inhabited.default", std::slice::from_ref(&sort_elem)),
                [elem.clone(), inhabited],
            );
            let value = Expr::apps(optional.clone(), [xs, i]);
            getter.lam(Expr::apps(
                cst("Option.getD", elem_level),
                [elem, value, default],
            ))
        };
        let type_ = t.pi(Expr::apps(cst("GetElem?", &levels), args.clone()));
        let fields = Expr::apps(cst("GetElem?.mk", &levels), args);
        let value = t.lam(Expr::apps(fields, [parent, optional, bang]));
        self.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![
                Name::from_string("u_1"),
                Name::from_string("u_2"),
                Name::from_string("u_3"),
            ],
            type_,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name,
            class_name: Name::from_string("GetElem?"),
            priority: 100, // Lean's standard low priority (Init/Notation.lean).
            type_: None,
            value: None,
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_indexing_registers_axiom_free_instances_and_preserves_imports() {
        let source = Environment::try_with_prelude().expect("checked source prelude");
        let imported = Environment::try_with_prelude_for_import().expect("checked import prelude");
        for (name, priority) in [
            (BOUNDED_BYTE_INDEX, LEAN_DEFAULT_INSTANCE_PRIORITY),
            (DECIDABLE_INDEX, 100),
        ] {
            let name = Name::from_string(name);
            assert_eq!(source.instance_priority(&name), Some(priority));
            assert!(source
                .get_const(&name)
                .expect("source declaration")
                .value
                .is_some());
            assert!(source.axiom_deps(&name).expect("source closure").is_empty());
            assert!(imported.get_const(&name).is_none());
            assert!(!imported.is_instance(&name));
        }
    }
}

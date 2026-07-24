// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod box_unsize;
mod general;
mod ref_unsize;

use super::*;
use crate::expr::{Expr, Pattern, Stmt};
use crate::memory::{Address, AllocId};
use crate::stmt::{FunctionDef, TraitDef};
use crate::types::{FunctionSignature, Lifetime, Mutability, ReceiverMode, RustType, UintType};
use crate::values::{FatPointer, FatPtrMetadata};

fn dog_type() -> RustType {
    RustType::Named {
        name: "Dog".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    }
}

fn animal_trait_type() -> RustType {
    RustType::DynTrait {
        trait_name: "Animal".to_string(),
        auto_traits: vec![],
    }
}

fn shared_u32_ref_type() -> RustType {
    RustType::Reference {
        lifetime: Lifetime::Named("a".to_string()),
        mutability: Mutability::Shared,
        inner: Box::new(RustType::Uint(UintType::U32)),
    }
}

fn register_animal_dispatch(interp: &mut Interpreter, speak_value: u32) {
    interp.ctx.register_full_trait_def(TraitDef::new(
        "Animal".to_string(),
        vec![FunctionSignature {
            name: "speak".to_string(),
            receiver: ReceiverMode::ByValue,
            params: vec![],
            ret: RustType::Uint(UintType::U32),
            is_async: false,
            type_params: vec![],
        }],
    ));
    interp
        .ctx
        .register_trait_impl("Animal".to_string(), dog_type());
    interp.ctx.add_impl_method(
        "Animal",
        "Dog",
        "speak".to_string(),
        "Dog_speak".to_string(),
    );
    interp.ctx.register_function(FunctionDef {
        name: "Dog_speak".to_string(),
        params: vec![("self".to_string(), dog_type())],
        ret_ty: RustType::Uint(UintType::U32),
        body: Expr::Literal(Value::u32(speak_value)),
        is_unsafe: false,
        is_async: false,
        type_params: vec![],
    });
}

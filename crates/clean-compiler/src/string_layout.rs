// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recognize the checked byte-backed String constructor telescope.
//!
//! These are source layouts, not Lean's C ABI: Clean's native Array and
//! ByteArray values retain their ordinary constructor cells. The String
//! carrier alone is a flat byte string and requires explicit conversion.

use clean_kernel::{BinderInfo, ConstructorVal, Environment, Expr, Level, Name};

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn plain_constructor(ctor: &ConstructorVal, name: &str, parent: &str, fields: u32) -> bool {
    ctor.name == Name::from_string(name)
        && ctor.inductive_name == Name::from_string(parent)
        && ctor.level_params.is_empty()
        && ctor.num_params == 0
        && ctor.num_fields == fields
        && ctor.constructor_idx == 0
}

fn array_constructor(ctor: &ConstructorVal) -> bool {
    if ctor.name != Name::from_string("Array.mk")
        || ctor.inductive_name != Name::from_string("Array")
        || ctor.level_params.len() != 1
        || ctor.num_params != 1
        || ctor.num_fields != 1
        || ctor.constructor_idx != 0
    {
        return false;
    }
    let u = Level::param(ctor.level_params[0].clone());
    let list = Expr::app(
        Expr::const_(Name::from_string("List"), vec![u.clone()]),
        Expr::bvar(0),
    );
    let array = Expr::app(
        Expr::const_(Name::from_string("Array"), vec![u.clone()]),
        Expr::bvar(1),
    );
    ctor.type_
        == Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::succ(u)),
            Expr::arrow(list, array),
        )
}

fn byte_array_constructor(ctor: &ConstructorVal) -> bool {
    plain_constructor(ctor, "ByteArray.mk", "ByteArray", 1)
        && ctor.type_
            == Expr::arrow(
                Expr::app(
                    Expr::const_(Name::from_string("Array"), vec![Level::zero()]),
                    constant("UInt8"),
                ),
                constant("ByteArray"),
            )
}

fn string_constructor(ctor: &ConstructorVal) -> bool {
    plain_constructor(ctor, "String.ofByteArray", "String", 2)
        && ctor.type_
            == Expr::arrow(
                constant("ByteArray"),
                Expr::arrow(
                    Expr::app(constant("ByteArray.IsValidUTF8"), Expr::bvar(0)),
                    constant("String"),
                ),
            )
}

/// Whether constructor metadata has the measured Array/ByteArray/String layout.
///
/// A same-named constructor with different fields receives ordinary lowering;
/// the native carrier audit continues to refuse such a String environment.
fn byte_array_string_constructors(ctors: &[&ConstructorVal]) -> bool {
    ["Array", "ByteArray", "String"].iter().all(|parent| {
        ctors
            .iter()
            .filter(|ctor| ctor.inductive_name == Name::from_string(parent))
            .count()
            == 1
    }) && ctors.iter().any(|ctor| array_constructor(ctor))
        && ctors.iter().any(|ctor| byte_array_constructor(ctor))
        && ctors.iter().any(|ctor| string_constructor(ctor))
}

/// Recognize the byte-backed String source layout in a kernel environment.
///
/// This does not establish declaration provenance or grant a native build
/// permission: the native audit independently owns that boundary.
pub fn has_byte_array_string_layout(env: &Environment) -> bool {
    let Some(array) = env.get_constructor(&Name::from_string("Array.mk")) else {
        return false;
    };
    let Some(bytes) = env.get_constructor(&Name::from_string("ByteArray.mk")) else {
        return false;
    };
    let Some(string) = env.get_constructor(&Name::from_string("String.ofByteArray")) else {
        return false;
    };
    let Some(validity) = env.get_const(&Name::from_string("ByteArray.IsValidUTF8")) else {
        return false;
    };
    if !array_constructor(array) || !byte_array_constructor(bytes) || !string_constructor(string) {
        return false;
    }
    let Some(array_level) = array.level_params.first() else {
        return false;
    };
    let sort = Expr::sort(Level::succ(Level::param(array_level.clone())));
    let array_type = Expr::arrow(sort.clone(), sort);
    env.get_inductive(&Name::from_string("Array"))
        .is_some_and(|ind| ind.type_ == array_type)
        && env
            .get_inductive(&Name::from_string("ByteArray"))
            .is_some_and(|ind| ind.type_ == Expr::type_())
        && env
            .get_inductive(&Name::from_string("String"))
            .is_some_and(|ind| ind.type_ == Expr::type_())
        && validity.type_ == Expr::arrow(constant("ByteArray"), Expr::prop())
        && byte_array_string_constructors(&env.constructors().collect::<Vec<_>>())
}

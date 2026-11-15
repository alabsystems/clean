// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Private native permission for the checked byte-backed source model.
//! Raw C and raw modules have no environment and cannot obtain this permission.

use clean_kernel::{
    BinderInfo, ConstantKind, DeclarationVerification, Environment, Expr, Level, Name,
};

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct StringLayoutPolicy {
    byte_backed: bool,
}

fn constant(name: &str) -> Expr {
    Expr::const_str(name)
}

fn checked(env: &Environment, name: &Name) -> bool {
    env.declaration_verification(name) == Some(DeclarationVerification::FullKernelCheck)
        && !env.is_unsafe(name)
        && !env.is_partial(name)
        && !env.is_staged_header(name)
        && !env.constant_needs_recheck(name)
        && env.axiom_deps(name).is_some_and(|debt| debt.is_empty())
}

fn projection(env: &Environment, name: &str, ty: Expr, value: Expr) -> bool {
    env.get_const(&Name::from_string(name)).is_some_and(|info| {
        info.kind == ConstantKind::Definition
            && info.type_ == ty
            && info.value.as_ref() == Some(&value)
    })
}

/// The shipped bridge traverses boxed List UInt8 and scalar UInt8 values.
/// Check the source constructor roles as well as the wrapper telescopes.
fn byte_list_layout(env: &Environment) -> bool {
    let Some(nil) = env.get_constructor(&Name::from_string("List.nil")) else {
        return false;
    };
    let Some(cons) = env.get_constructor(&Name::from_string("List.cons")) else {
        return false;
    };
    if nil.level_params.len() != 1 || cons.level_params.len() != 1 {
        return false;
    }
    let list = |u: Level, a| Expr::app(Expr::const_(Name::from_string("List"), vec![u]), a);
    let u = Level::param(nil.level_params[0].clone());
    let nil_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(Level::succ(u.clone())),
        list(u, Expr::bvar(0)),
    );
    let u = Level::param(cons.level_params[0].clone());
    let cons_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(Level::succ(u.clone())),
        Expr::arrow(
            Expr::bvar(0),
            Expr::arrow(list(u.clone(), Expr::bvar(1)), list(u, Expr::bvar(2))),
        ),
    );
    let list_roles = nil.inductive_name == Name::from_string("List")
        && nil.num_params == 1
        && nil.num_fields == 0
        && nil.constructor_idx == 0
        && nil.type_ == nil_type
        && cons.inductive_name == Name::from_string("List")
        && cons.num_params == 1
        && cons.num_fields == 2
        && cons.constructor_idx == 1
        && cons.type_ == cons_type
        && env
            .get_inductive(&Name::from_string("List"))
            .is_some_and(|ind| {
                let [level] = ind.level_params.as_slice() else {
                    return false;
                };
                let sort = Expr::sort(Level::succ(Level::param(level.clone())));
                ind.type_ == Expr::arrow(sort.clone(), sort)
                    && ind.num_params == 1
                    && ind.num_indices == 0
                    && ind.is_recursive
                    && ind.constructor_names
                        == [
                            Name::from_string("List.nil"),
                            Name::from_string("List.cons"),
                        ]
            });
    let Some(byte) = env.get_constructor(&Name::from_string("UInt8.ofBitVec")) else {
        return false;
    };
    // The actual source telescope preserves numeral elaboration here.
    let eight = Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            constant("Nat"),
            Expr::nat_lit(8),
            Expr::app(constant("instOfNatNat"), Expr::nat_lit(8)),
        ],
    );
    list_roles
        && byte.inductive_name == Name::from_string("UInt8")
        && byte.level_params.is_empty()
        && byte.num_params == 0
        && byte.num_fields == 1
        && byte.constructor_idx == 0
        && byte.type_ == Expr::arrow(Expr::app(constant("BitVec"), eight), constant("UInt8"))
        && env
            .get_inductive(&Name::from_string("UInt8"))
            .is_some_and(|ind| {
                ind.type_ == Expr::type_()
                    && ind.num_params == 0
                    && ind.num_indices == 0
                    && !ind.is_recursive
                    && ind.constructor_names == [Name::from_string("UInt8.ofBitVec")]
            })
}

fn validity_layout(env: &Environment) -> bool {
    let name = Name::from_string("ByteArray.IsValidUTF8");
    let Some(ind) = env.get_inductive(&name) else {
        return false;
    };
    let Some(ctor) = env.get_constructor(&name.clone().str("intro")) else {
        return false;
    };
    let bytes = constant("ByteArray");
    let chars = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        constant("Char"),
    );
    let equality = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            bytes.clone(),
            Expr::bvar(1),
            Expr::app(constant("List.utf8Encode"), Expr::bvar(0)),
        ],
    );
    ind.num_params == 1
        && ind.num_indices == 0
        && !ind.is_recursive
        && ind.constructor_names == [name.clone().str("intro")]
        && ctor.inductive_name == name
        && ctor.num_params == 1
        && ctor.num_fields == 2
        && ctor.constructor_idx == 0
        && ctor.level_params.is_empty()
        && ctor.type_
            == Expr::pi(
                BinderInfo::Implicit,
                bytes,
                Expr::arrow(
                    chars,
                    Expr::arrow(
                        equality,
                        Expr::app(constant("ByteArray.IsValidUTF8"), Expr::bvar(2)),
                    ),
                ),
            )
}

impl StringLayoutPolicy {
    pub(crate) fn from_env(env: &Environment) -> Self {
        if !clean_compiler::string_layout::has_byte_array_string_layout(env)
            || !byte_list_layout(env)
            || !validity_layout(env)
            || ![
                "Array",
                "Array.mk",
                "Array.toList",
                "ByteArray",
                "ByteArray.mk",
                "ByteArray.data",
                "String",
                "String.ofByteArray",
                "String.toByteArray",
                "String.rec",
                "ByteArray.IsValidUTF8",
                "ByteArray.IsValidUTF8.intro",
                "List",
                "List.nil",
                "List.cons",
                "UInt8",
                "UInt8.ofBitVec",
            ]
            .iter()
            .all(|name| checked(env, &Name::from_string(name)))
        {
            return Self::default();
        }
        let bytes = constant("ByteArray");
        let string = constant("String");
        let byte_array = Expr::app(
            Expr::const_(Name::from_string("Array"), vec![Level::zero()]),
            constant("UInt8"),
        );
        let Some(array) = env.get_const(&Name::from_string("Array.toList")) else {
            return Self::default();
        };
        let [level] = array.level_params.as_slice() else {
            return Self::default();
        };
        let u = Level::param(level.clone());
        let sort = Expr::sort(Level::succ(u.clone()));
        let array_a = Expr::app(
            Expr::const_(Name::from_string("Array"), vec![u.clone()]),
            Expr::bvar(0),
        );
        let list_a = Expr::app(
            Expr::const_(Name::from_string("List"), vec![u]),
            Expr::bvar(1),
        );
        let array_type = Expr::pi(
            BinderInfo::Implicit,
            sort.clone(),
            Expr::arrow(array_a.clone(), list_a),
        );
        let array_value = Expr::lam(
            BinderInfo::Default,
            sort,
            Expr::lam(
                BinderInfo::Default,
                array_a,
                Expr::proj(Name::from_string("Array"), 0, Expr::bvar(0)),
            ),
        );
        Self {
            byte_backed: projection(env, "Array.toList", array_type, array_value)
                && projection(
                    env,
                    "ByteArray.data",
                    Expr::arrow(bytes.clone(), byte_array),
                    Expr::lam(
                        BinderInfo::Default,
                        bytes.clone(),
                        Expr::proj(Name::from_string("ByteArray"), 0, Expr::bvar(0)),
                    ),
                )
                && projection(
                    env,
                    "String.toByteArray",
                    Expr::arrow(string.clone(), bytes),
                    Expr::lam(
                        BinderInfo::Default,
                        string,
                        Expr::proj(Name::from_string("String"), 0, Expr::bvar(0)),
                    ),
                ),
        }
    }

    pub(crate) fn permits_byte_backed_bodies(self) -> bool {
        self.byte_backed
    }

    pub(crate) fn permits_source_decl(self, env: &Environment, name: &Name) -> bool {
        self.byte_backed && checked(env, name)
    }
}

#[cfg(test)]
#[path = "native_string_layout_policy_tests.rs"]
mod tests;

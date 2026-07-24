// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod batch;
mod parser;
mod translation;

use super::{Constr, ConstructRef, CoqName, InductiveRef, UniverseInstance, UniverseLevel};

pub(super) fn nat_ref() -> InductiveRef {
    InductiveRef {
        name: CoqName::from_dotted("Coq.Init.Datatypes.nat"),
        index: 0,
        universes: UniverseInstance::default(),
    }
}

pub(super) fn bool_ref() -> InductiveRef {
    InductiveRef {
        name: CoqName::from_dotted("Coq.Init.Datatypes.bool"),
        index: 0,
        universes: UniverseInstance::default(),
    }
}

pub(super) fn list_ref() -> InductiveRef {
    InductiveRef {
        name: CoqName::from_dotted("Coq.Init.Datatypes.list"),
        index: 0,
        universes: UniverseInstance {
            levels: vec![UniverseLevel::Param("u".to_string())],
        },
    }
}

pub(super) fn eq_ref() -> InductiveRef {
    InductiveRef {
        name: CoqName::from_dotted("Coq.Init.Logic.eq"),
        index: 0,
        universes: UniverseInstance::default(),
    }
}

pub(super) fn nat_zero() -> Constr {
    Constr::Construct(ConstructRef {
        inductive: CoqName::from_dotted("Coq.Init.Datatypes.nat"),
        constructor_index: 1,
        constructor_name: Some("zero".to_string()),
        universes: UniverseInstance::default(),
    })
}

pub(super) fn nat_succ(arg: Constr) -> Constr {
    Constr::app(
        Constr::Construct(ConstructRef {
            inductive: CoqName::from_dotted("Coq.Init.Datatypes.nat"),
            constructor_index: 2,
            constructor_name: Some("succ".to_string()),
            universes: UniverseInstance::default(),
        }),
        vec![arg],
    )
}

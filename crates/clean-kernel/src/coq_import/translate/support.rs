// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared translation helpers.

use crate::{
    coq_import::{
        CoqImportError, CoqImportResult, CoqName, CoqSort, UniverseInstance, UniverseLevel,
    },
    Expr, Level, LevelVec, Name,
};

pub(super) fn translate_name(name: &str) -> Name {
    Name::from_string(name)
}

pub(super) fn translate_coq_name(name: &CoqName) -> Name {
    translate_name(&name.as_dotted())
}

pub(super) fn sanitize_name_component(component: &str) -> String {
    component
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

pub(super) fn translate_sort(sort: &CoqSort) -> CoqImportResult<Expr> {
    match sort {
        CoqSort::Prop => Ok(Expr::prop()),
        CoqSort::Set => Ok(Expr::type_()),
        CoqSort::Type(level) => Ok(Expr::sort(Level::succ(translate_level(level)?))),
    }
}

pub(super) fn translate_universe_instance(
    instance: &UniverseInstance,
) -> CoqImportResult<LevelVec> {
    let mut levels = LevelVec::new();
    for level in &instance.levels {
        levels.push(translate_level(level)?);
    }
    Ok(levels)
}

fn translate_level(level: &UniverseLevel) -> CoqImportResult<Level> {
    match level {
        UniverseLevel::Zero => Ok(Level::zero()),
        UniverseLevel::Succ(inner) => Ok(Level::succ(translate_level(inner)?)),
        UniverseLevel::Max(levels) => {
            let mut iter = levels.iter();
            let Some(first) = iter.next() else {
                return Err(CoqImportError::EmptyMaxUniverse);
            };
            let mut out = translate_level(first)?;
            for level in iter {
                out = Level::max(out, translate_level(level)?);
            }
            Ok(out)
        }
        UniverseLevel::IMax(left, right) => {
            Ok(Level::imax(translate_level(left)?, translate_level(right)?))
        }
        UniverseLevel::Param(name) => Ok(Level::param(Name::from_string(name))),
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory VM helper routines.

use super::{
    name::OtName,
    object::OtObject,
    term::{OtTerm, OtVariable},
    ty::OtType,
    OpenTheoryError, OpenTheoryResult,
};

pub(crate) type OtTypeSubstitution = Vec<(OtName, OtType)>;
pub(crate) type OtTermSubstitution = Vec<(OtVariable, OtTerm)>;

pub(crate) fn ensure_bool_term(command: &'static str, term: &OtTerm) -> OpenTheoryResult<()> {
    let ty = term.ty()?;
    if ty.is_bool() {
        Ok(())
    } else {
        Err(OpenTheoryError::ExpectedBoolTerm { command, ty })
    }
}

pub(crate) fn ensure_global_name(command: &'static str, name: &OtName) -> OpenTheoryResult<()> {
    if name.is_global() {
        Ok(())
    } else {
        Err(OpenTheoryError::ExpectedGlobalName {
            command,
            name: name.clone(),
        })
    }
}

pub(crate) fn expected_object(
    command: &'static str,
    expected: &'static str,
    actual: &OtObject,
) -> OpenTheoryError {
    OpenTheoryError::ExpectedObject {
        command,
        expected,
        actual: actual.kind_name(),
    }
}

pub(crate) fn extract_name_var_pair(object: &OtObject) -> OpenTheoryResult<(OtName, OtVariable)> {
    let OtObject::List(items) = object else {
        return Err(expected_object("defineConstList", "list", object));
    };
    if items.len() != 2 {
        return Err(OpenTheoryError::MalformedObject {
            command: "defineConstList",
            detail: "expected a [name, variable] pair".to_string(),
        });
    }
    let name = match &items[0] {
        OtObject::Name(name) => name.clone(),
        other => return Err(expected_object("defineConstList", "name", other)),
    };
    let variable = match &items[1] {
        OtObject::Var(variable) => variable.clone(),
        other => return Err(expected_object("defineConstList", "variable", other)),
    };
    Ok((name, variable))
}

pub(crate) fn extract_variable_definition(
    hypothesis: &OtTerm,
) -> OpenTheoryResult<(OtVariable, OtTerm)> {
    let (lhs, rhs) = hypothesis
        .dest_eq()
        .ok_or(OpenTheoryError::MalformedObject {
            command: "defineConstList",
            detail: "expected a hypothesis of the form v = t".to_string(),
        })?;
    let OtTerm::Var(variable) = lhs else {
        return Err(OpenTheoryError::MalformedObject {
            command: "defineConstList",
            detail: "expected a variable on the left-hand side of a defining equality".to_string(),
        });
    };
    Ok((variable.clone(), rhs.clone()))
}

pub(crate) fn extract_substitution(
    object: &[OtObject],
) -> OpenTheoryResult<(OtTypeSubstitution, OtTermSubstitution)> {
    if object.len() != 2 {
        return Err(OpenTheoryError::MalformedObject {
            command: "subst",
            detail: "expected [typeSubst, termSubst]".to_string(),
        });
    }

    let type_subs = match &object[0] {
        OtObject::List(entries) => entries
            .iter()
            .map(|entry| {
                let OtObject::List(pair) = entry else {
                    return Err(OpenTheoryError::MalformedObject {
                        command: "subst",
                        detail: "type substitution entries must be [name, type]".to_string(),
                    });
                };
                if pair.len() != 2 {
                    return Err(OpenTheoryError::MalformedObject {
                        command: "subst",
                        detail: "type substitution entries must be [name, type]".to_string(),
                    });
                }
                let name = match &pair[0] {
                    OtObject::Name(name) => {
                        ensure_global_name("subst", name)?;
                        name.clone()
                    }
                    other => return Err(expected_object("subst", "name", other)),
                };
                let ty = match &pair[1] {
                    OtObject::Type(ty) => ty.clone(),
                    other => return Err(expected_object("subst", "type", other)),
                };
                Ok((name, ty))
            })
            .collect::<OpenTheoryResult<Vec<_>>>()?,
        other => return Err(expected_object("subst", "list", other)),
    };

    let term_subs = match &object[1] {
        OtObject::List(entries) => entries
            .iter()
            .map(|entry| {
                let OtObject::List(pair) = entry else {
                    return Err(OpenTheoryError::MalformedObject {
                        command: "subst",
                        detail: "term substitution entries must be [variable, term]".to_string(),
                    });
                };
                if pair.len() != 2 {
                    return Err(OpenTheoryError::MalformedObject {
                        command: "subst",
                        detail: "term substitution entries must be [variable, term]".to_string(),
                    });
                }
                let variable = match &pair[0] {
                    OtObject::Var(variable) => variable.clone(),
                    other => return Err(expected_object("subst", "variable", other)),
                };
                let term = match &pair[1] {
                    OtObject::Term(term) => term.clone(),
                    other => return Err(expected_object("subst", "term", other)),
                };
                Ok((variable, term))
            })
            .collect::<OpenTheoryResult<Vec<_>>>()?,
        other => return Err(expected_object("subst", "list", other)),
    };

    Ok((type_subs, term_subs))
}

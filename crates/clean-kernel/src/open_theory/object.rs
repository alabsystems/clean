// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory VM objects.

use super::{
    name::OtName,
    term::{OtConstant, OtTerm, OtTheorem, OtVariable},
    ty::{OtType, OtTypeOperator},
};

/// OpenTheory VM object.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum OtObject {
    Num(i64),
    Name(OtName),
    List(Vec<OtObject>),
    TypeOp(OtTypeOperator),
    Type(OtType),
    Const(OtConstant),
    Var(OtVariable),
    Term(OtTerm),
    Thm(OtTheorem),
}

impl OtObject {
    #[must_use]
    pub fn kind_name(&self) -> &'static str {
        match self {
            Self::Num(_) => "number",
            Self::Name(_) => "name",
            Self::List(_) => "list",
            Self::TypeOp(_) => "type operator",
            Self::Type(_) => "type",
            Self::Const(_) => "constant",
            Self::Var(_) => "variable",
            Self::Term(_) => "term",
            Self::Thm(_) => "theorem",
        }
    }
}

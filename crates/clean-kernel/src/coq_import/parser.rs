// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser for normalized SerAPI-style S-expressions.
//!
//! The real SerAPI output is rich and version-dependent. This scaffold accepts a
//! small, explicit subset that keeps the Coq import pipeline testable:
//! - atoms and lists in standard S-expression syntax
//! - optional JSON wrappers whose payload contains S-expression strings
//! - normalized declaration forms (`definition`, `axiom`, `inductive`, ...)

use super::types::{
    Binder, CaseBranch, CaseInfo, CastKind, CoFixTerm, ConstantDecl, ConstantDeclKind, Constr,
    ConstructRef, ConstructorDecl, CoqBinderKind, CoqName, CoqSort, FixBody, FixTerm, GlobalDecl,
    InductiveBody, InductiveKind, InductiveRef, MutualInductiveDecl, ProjectionRef,
    UniverseInstance, UniverseLevel,
};
use super::{CoqImportError, CoqImportResult};
use serde_json::Value;

/// Generic S-expression node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

/// Parse one S-expression.
pub fn parse_sexp(input: &str) -> CoqImportResult<Sexp> {
    let mut sexps = parse_all_sexps(input)?;
    if sexps.len() != 1 {
        return Err(CoqImportError::UnexpectedToken {
            context: "single s-expression",
            token: format!("{} top-level forms", sexps.len()),
        });
    }
    Ok(sexps.remove(0))
}

/// Parse one Coq `Constr` term from S-expression syntax.
pub fn parse_constr(input: &str) -> CoqImportResult<Constr> {
    let sexp = parse_sexp(input)?;
    parse_constr_from_sexp(&sexp)
}

/// Parse one top-level declaration.
pub fn parse_declaration(input: &str) -> CoqImportResult<GlobalDecl> {
    let mut decls = parse_declarations(input)?;
    if decls.len() != 1 {
        return Err(CoqImportError::UnexpectedToken {
            context: "single declaration",
            token: format!("{} declarations", decls.len()),
        });
    }
    Ok(decls.remove(0))
}

/// Parse one or more top-level declarations.
pub fn parse_declarations(input: &str) -> CoqImportResult<Vec<GlobalDecl>> {
    let trimmed = input.trim_start();
    if matches!(trimmed.chars().next(), Some('{') | Some('[') | Some('"')) {
        let json = serde_json::from_str::<Value>(input)?;
        return parse_declarations_from_json(&json);
    }
    parse_declarations_from_sexp_input(input)
}

fn parse_declarations_from_json(value: &Value) -> CoqImportResult<Vec<GlobalDecl>> {
    match value {
        Value::String(sexp) => parse_declarations_from_sexp_input(sexp),
        Value::Array(items) => {
            let mut out = Vec::new();
            for item in items {
                out.extend(parse_declarations_from_json(item)?);
            }
            Ok(out)
        }
        Value::Object(map) => {
            if let Some(value) = map.get("sexp") {
                return parse_declarations_from_json(value);
            }
            if let Some(value) = map.get("decls") {
                return parse_declarations_from_json(value);
            }
            Err(CoqImportError::UnsupportedJsonShape)
        }
        _ => Err(CoqImportError::UnsupportedJsonShape),
    }
}

fn parse_declarations_from_sexp_input(input: &str) -> CoqImportResult<Vec<GlobalDecl>> {
    let sexps = parse_all_sexps(input)?;
    if sexps.len() == 1 {
        if let Some(decls) = parse_declaration_wrapper(&sexps[0])? {
            return Ok(decls);
        }
    }

    sexps.iter().map(parse_declaration_from_sexp).collect()
}

fn parse_declaration_wrapper(sexp: &Sexp) -> CoqImportResult<Option<Vec<GlobalDecl>>> {
    let items = expect_list(sexp, "declaration wrapper")?;
    if items.is_empty() {
        return Ok(Some(Vec::new()));
    }

    if head_is(items, "decls") || head_is(items, "declarations") {
        return Ok(Some(
            items[1..]
                .iter()
                .map(parse_declaration_from_sexp)
                .collect::<CoqImportResult<Vec<_>>>()?,
        ));
    }

    let all_decls = items.iter().all(is_declaration_form);
    if all_decls {
        return Ok(Some(
            items
                .iter()
                .map(parse_declaration_from_sexp)
                .collect::<CoqImportResult<Vec<_>>>()?,
        ));
    }

    Ok(None)
}

fn parse_all_sexps(input: &str) -> CoqImportResult<Vec<Sexp>> {
    let mut parser = Parser::new(input);
    let mut sexps = Vec::new();
    parser.skip_ws_and_comments();
    while !parser.is_eof() {
        sexps.push(parser.parse_expr("s-expression")?);
        parser.skip_ws_and_comments();
    }
    if sexps.is_empty() {
        return Err(CoqImportError::UnexpectedEof {
            context: "s-expression",
        });
    }
    Ok(sexps)
}

fn parse_declaration_from_sexp(sexp: &Sexp) -> CoqImportResult<GlobalDecl> {
    let items = expect_list(sexp, "declaration")?;
    let head = head_atom(items, "declaration")?;
    match head.to_ascii_lowercase().as_str() {
        "constant" => Ok(GlobalDecl::Constant(parse_constant_decl(
            items,
            ConstantDeclKind::Definition,
        )?)),
        "definition" => Ok(GlobalDecl::Constant(parse_constant_decl(
            items,
            ConstantDeclKind::Definition,
        )?)),
        "axiom" => Ok(GlobalDecl::Constant(parse_constant_decl(
            items,
            ConstantDeclKind::Axiom,
        )?)),
        "theorem" => Ok(GlobalDecl::Constant(parse_constant_decl(
            items,
            ConstantDeclKind::Theorem,
        )?)),
        "opaque" => Ok(GlobalDecl::Constant(parse_constant_decl(
            items,
            ConstantDeclKind::Opaque,
        )?)),
        "inductive" => Ok(GlobalDecl::Inductive(parse_inductive_decl(
            items,
            InductiveKind::Inductive,
        )?)),
        "coinductive" => Ok(GlobalDecl::Inductive(parse_inductive_decl(
            items,
            InductiveKind::CoInductive,
        )?)),
        _ => Err(CoqImportError::UnexpectedToken {
            context: "declaration",
            token: head.to_string(),
        }),
    }
}

fn parse_constant_decl(
    items: &[Sexp],
    default_kind: ConstantDeclKind,
) -> CoqImportResult<ConstantDecl> {
    let fields = &items[1..];
    let kind = if let Some(kind) = find_field(fields, "kind") {
        parse_constant_decl_kind(single_field_value(kind, "constant kind")?)?
    } else {
        default_kind
    };
    let name = parse_name(single_field_value(
        require_field(fields, "constant declaration", "name")?,
        "constant name",
    )?)?;
    let universe_params =
        if let Some(field) = find_field_any(fields, &["levels", "universe_params"]) {
            parse_string_list(field)?
        } else {
            Vec::new()
        };
    let type_ = parse_constr_from_sexp(single_field_value(
        require_field(fields, "constant declaration", "type")?,
        "constant type",
    )?)?;
    let value = if let Some(field) = find_field(fields, "value") {
        Some(parse_constr_from_sexp(single_field_value(
            field,
            "constant value",
        )?)?)
    } else {
        None
    };

    Ok(ConstantDecl {
        kind,
        name,
        universe_params,
        type_,
        value,
    })
}

fn parse_inductive_decl(
    items: &[Sexp],
    default_kind: InductiveKind,
) -> CoqImportResult<MutualInductiveDecl> {
    let fields = &items[1..];
    let kind = if let Some(kind) = find_field(fields, "kind") {
        parse_inductive_kind(single_field_value(kind, "inductive kind")?)?
    } else {
        default_kind
    };
    let universe_params =
        if let Some(field) = find_field_any(fields, &["levels", "universe_params"]) {
            parse_string_list(field)?
        } else {
            Vec::new()
        };
    let params = if let Some(field) = find_field(fields, "params") {
        normalize_collection(field)?
            .iter()
            .map(parse_binder)
            .collect::<CoqImportResult<Vec<_>>>()?
    } else {
        Vec::new()
    };
    let num_params = if let Some(field) = find_field(fields, "num_params") {
        parse_u32(single_field_value(field, "num_params")?, "num_params")?
    } else {
        // Parameter lists are parsed from input; reject counts beyond u32
        // instead of panicking.
        u32::try_from(params.len()).map_err(|_| CoqImportError::InvalidNumber {
            context: "num_params",
            value: params.len().to_string(),
        })?
    };
    let bodies = normalize_collection(require_field(
        fields,
        "mutual inductive declaration",
        "bodies",
    )?)?
    .iter()
    .map(parse_inductive_body)
    .collect::<CoqImportResult<Vec<_>>>()?;

    Ok(MutualInductiveDecl {
        kind,
        universe_params,
        num_params,
        params,
        bodies,
    })
}

fn parse_inductive_body(sexp: &Sexp) -> CoqImportResult<InductiveBody> {
    let items = expect_list(sexp, "inductive body")?;
    if !head_is(items, "body") && !head_is(items, "inductive_body") {
        return Err(CoqImportError::UnexpectedToken {
            context: "inductive body",
            token: head_atom(items, "inductive body")?.to_string(),
        });
    }
    let fields = &items[1..];
    let name = parse_name(single_field_value(
        require_field(fields, "inductive body", "name")?,
        "inductive body name",
    )?)?;
    let type_ = parse_constr_from_sexp(single_field_value(
        require_field(fields, "inductive body", "type")?,
        "inductive body type",
    )?)?;
    let constructors =
        normalize_collection(require_field(fields, "inductive body", "constructors")?)?
            .iter()
            .map(parse_constructor_decl)
            .collect::<CoqImportResult<Vec<_>>>()?;

    Ok(InductiveBody {
        name,
        type_,
        constructors,
    })
}

fn parse_constructor_decl(sexp: &Sexp) -> CoqImportResult<ConstructorDecl> {
    let items = expect_list(sexp, "constructor declaration")?;
    if !head_is(items, "ctor") && !head_is(items, "constructor") {
        return Err(CoqImportError::UnexpectedToken {
            context: "constructor declaration",
            token: head_atom(items, "constructor declaration")?.to_string(),
        });
    }
    let fields = &items[1..];
    let name = parse_name(single_field_value(
        require_field(fields, "constructor declaration", "name")?,
        "constructor name",
    )?)?;
    let type_ = parse_constr_from_sexp(single_field_value(
        require_field(fields, "constructor declaration", "type")?,
        "constructor type",
    )?)?;
    Ok(ConstructorDecl { name, type_ })
}

fn parse_constr_from_sexp(sexp: &Sexp) -> CoqImportResult<Constr> {
    match sexp {
        Sexp::Atom(atom) => parse_atom_constr(atom),
        Sexp::List(items) => parse_list_constr(items),
    }
}

fn parse_atom_constr(atom: &str) -> CoqImportResult<Constr> {
    if atom.eq_ignore_ascii_case("prop") || atom.eq_ignore_ascii_case("set") {
        return Ok(Constr::Sort(parse_sort_atom(atom)?));
    }
    Ok(Constr::Var(CoqName::from_dotted(atom)))
}

fn parse_list_constr(items: &[Sexp]) -> CoqImportResult<Constr> {
    if items.is_empty() {
        return Err(CoqImportError::UnexpectedEof {
            context: "Constr node",
        });
    }
    let head = head_atom(items, "Constr node")?;
    match head.to_ascii_lowercase().as_str() {
        "rel" => Ok(Constr::Rel(parse_u32(&items[1], "Rel index")?)),
        "var" => Ok(Constr::Var(parse_name(&items[1])?)),
        "meta" => Ok(Constr::Meta(parse_u32(&items[1], "Meta index")?)),
        "evar" => parse_evar(items),
        "sort" => Ok(Constr::Sort(parse_sort(&items[1])?)),
        "cast" => parse_cast(items),
        "prod" => parse_prod(items),
        "lambda" | "lam" => parse_lambda(items),
        "letin" | "let_in" => parse_letin(items),
        "app" => parse_app(items),
        "const" => parse_const(items),
        "ind" => parse_ind(items),
        "construct" | "ctor" => parse_construct(items),
        "case" => parse_case(items),
        "fix" => parse_fix(items),
        "cofix" => parse_cofix(items),
        "proj" => parse_proj(items),
        _ => Err(CoqImportError::UnexpectedToken {
            context: "Constr node",
            token: head.to_string(),
        }),
    }
}

fn parse_evar(items: &[Sexp]) -> CoqImportResult<Constr> {
    if has_any_field(&items[1..], &["id", "args"]) {
        let fields = &items[1..];
        let id = parse_u32(
            single_field_value(require_field(fields, "Evar", "id")?, "Evar id")?,
            "Evar id",
        )?;
        let args = if let Some(field) = find_field(fields, "args") {
            normalize_collection(field)?
                .iter()
                .map(parse_constr_from_sexp)
                .collect::<CoqImportResult<Vec<_>>>()?
        } else {
            Vec::new()
        };
        return Ok(Constr::Evar { id, args });
    }

    let id = parse_u32(&items[1], "Evar id")?;
    let args = if items.len() > 2 {
        normalize_collection_from_item(&items[2])?
            .iter()
            .map(parse_constr_from_sexp)
            .collect::<CoqImportResult<Vec<_>>>()?
    } else {
        Vec::new()
    };
    Ok(Constr::Evar { id, args })
}

fn parse_cast(items: &[Sexp]) -> CoqImportResult<Constr> {
    if has_any_field(&items[1..], &["term", "kind", "type"]) {
        let fields = &items[1..];
        return Ok(Constr::Cast {
            term: Box::new(parse_constr_from_sexp(single_field_value(
                require_field(fields, "Cast", "term")?,
                "Cast term",
            )?)?),
            kind: parse_cast_kind(single_field_value(
                require_field(fields, "Cast", "kind")?,
                "Cast kind",
            )?)?,
            ty: Box::new(parse_constr_from_sexp(single_field_value(
                require_field(fields, "Cast", "type")?,
                "Cast type",
            )?)?),
        });
    }

    Ok(Constr::Cast {
        term: Box::new(parse_constr_from_sexp(&items[1])?),
        kind: parse_cast_kind(&items[2])?,
        ty: Box::new(parse_constr_from_sexp(&items[3])?),
    })
}

fn parse_prod(items: &[Sexp]) -> CoqImportResult<Constr> {
    Ok(Constr::Prod {
        binder: parse_binder(&items[1])?,
        body: Box::new(parse_constr_from_sexp(&items[2])?),
    })
}

fn parse_lambda(items: &[Sexp]) -> CoqImportResult<Constr> {
    Ok(Constr::Lambda {
        binder: parse_binder(&items[1])?,
        body: Box::new(parse_constr_from_sexp(&items[2])?),
    })
}

fn parse_letin(items: &[Sexp]) -> CoqImportResult<Constr> {
    if has_any_field(&items[1..], &["name", "type", "value", "body"]) {
        let fields = &items[1..];
        let name = find_field(fields, "name")
            .map(|field| parse_optional_name(single_field_value(field, "let name")?))
            .transpose()?
            .flatten();
        return Ok(Constr::LetIn {
            name,
            type_: Box::new(parse_constr_from_sexp(single_field_value(
                require_field(fields, "LetIn", "type")?,
                "let type",
            )?)?),
            value: Box::new(parse_constr_from_sexp(single_field_value(
                require_field(fields, "LetIn", "value")?,
                "let value",
            )?)?),
            body: Box::new(parse_constr_from_sexp(single_field_value(
                require_field(fields, "LetIn", "body")?,
                "let body",
            )?)?),
        });
    }

    Ok(Constr::LetIn {
        name: parse_optional_name(&items[1])?,
        type_: Box::new(parse_constr_from_sexp(&items[2])?),
        value: Box::new(parse_constr_from_sexp(&items[3])?),
        body: Box::new(parse_constr_from_sexp(&items[4])?),
    })
}

fn parse_app(items: &[Sexp]) -> CoqImportResult<Constr> {
    if has_any_field(&items[1..], &["func", "args"]) {
        let fields = &items[1..];
        let func = parse_constr_from_sexp(single_field_value(
            require_field(fields, "App", "func")?,
            "application function",
        )?)?;
        let args = normalize_collection(require_field(fields, "App", "args")?)?
            .iter()
            .map(parse_constr_from_sexp)
            .collect::<CoqImportResult<Vec<_>>>()?;
        if args.is_empty() {
            return Err(CoqImportError::EmptyApplication);
        }
        return Ok(Constr::app(func, args));
    }

    let func = parse_constr_from_sexp(&items[1])?;
    let args = if items.len() == 3 && matches!(&items[2], Sexp::List(_)) {
        normalize_collection_from_item(&items[2])?
            .iter()
            .map(parse_constr_from_sexp)
            .collect::<CoqImportResult<Vec<_>>>()?
    } else {
        items[2..]
            .iter()
            .map(parse_constr_from_sexp)
            .collect::<CoqImportResult<Vec<_>>>()?
    };
    if args.is_empty() {
        return Err(CoqImportError::EmptyApplication);
    }
    Ok(Constr::app(func, args))
}

fn parse_const(items: &[Sexp]) -> CoqImportResult<Constr> {
    if has_any_field(&items[1..], &["name", "universes"]) {
        let fields = &items[1..];
        return Ok(Constr::Const {
            name: parse_name(single_field_value(
                require_field(fields, "Const", "name")?,
                "const name",
            )?)?,
            universes: if let Some(field) = find_field(fields, "universes") {
                parse_universe_instance(field)?
            } else {
                UniverseInstance::default()
            },
        });
    }

    Ok(Constr::Const {
        name: parse_name(&items[1])?,
        universes: if items.len() > 2 {
            parse_universe_instance_from_item(&items[2])?
        } else {
            UniverseInstance::default()
        },
    })
}

fn parse_ind(items: &[Sexp]) -> CoqImportResult<Constr> {
    if has_any_field(&items[1..], &["name", "index", "universes"]) {
        let fields = &items[1..];
        return Ok(Constr::Ind(InductiveRef {
            name: parse_name(single_field_value(
                require_field(fields, "Ind", "name")?,
                "inductive name",
            )?)?,
            index: if let Some(field) = find_field(fields, "index") {
                parse_u32(
                    single_field_value(field, "inductive index")?,
                    "inductive index",
                )?
            } else {
                0
            },
            universes: if let Some(field) = find_field(fields, "universes") {
                parse_universe_instance(field)?
            } else {
                UniverseInstance::default()
            },
        }));
    }

    Ok(Constr::Ind(InductiveRef {
        name: parse_name(&items[1])?,
        index: if items.len() > 2 {
            parse_u32(&items[2], "inductive index")?
        } else {
            0
        },
        universes: if items.len() > 3 {
            parse_universe_instance_from_item(&items[3])?
        } else {
            UniverseInstance::default()
        },
    }))
}

fn parse_construct(items: &[Sexp]) -> CoqImportResult<Constr> {
    if has_any_field(&items[1..], &["inductive", "index", "name", "universes"]) {
        let fields = &items[1..];
        return Ok(Constr::Construct(ConstructRef {
            inductive: parse_name(single_field_value(
                require_field(fields, "Construct", "inductive")?,
                "constructor inductive",
            )?)?,
            constructor_index: parse_u32(
                single_field_value(
                    require_field(fields, "Construct", "index")?,
                    "constructor index",
                )?,
                "constructor index",
            )?,
            constructor_name: find_field(fields, "name")
                .map(|field| parse_optional_name(single_field_value(field, "constructor name")?))
                .transpose()?
                .flatten(),
            universes: if let Some(field) = find_field(fields, "universes") {
                parse_universe_instance(field)?
            } else {
                UniverseInstance::default()
            },
        }));
    }

    Ok(Constr::Construct(ConstructRef {
        inductive: parse_name(&items[1])?,
        constructor_index: parse_u32(&items[2], "constructor index")?,
        constructor_name: if items.len() > 3 && !matches!(&items[3], Sexp::List(_)) {
            parse_optional_name(&items[3])?
        } else {
            None
        },
        universes: if items.len() > 4 {
            parse_universe_instance_from_item(&items[4])?
        } else if items.len() > 3 && matches!(&items[3], Sexp::List(_)) {
            parse_universe_instance_from_item(&items[3])?
        } else {
            UniverseInstance::default()
        },
    }))
}

fn parse_case(items: &[Sexp]) -> CoqImportResult<Constr> {
    let fields = &items[1..];
    let inductive = parse_name(single_field_value(
        require_field(fields, "Case", "inductive")?,
        "case inductive",
    )?)?;
    let universes = if let Some(field) = find_field(fields, "universes") {
        parse_universe_instance(field)?
    } else {
        UniverseInstance::default()
    };
    let eliminator = find_field(fields, "eliminator")
        .map(|field| parse_name(single_field_value(field, "case eliminator")?))
        .transpose()?;
    let parameters = if let Some(field) = find_field(fields, "parameters") {
        normalize_collection(field)?
            .iter()
            .map(parse_constr_from_sexp)
            .collect::<CoqImportResult<Vec<_>>>()?
    } else {
        Vec::new()
    };
    let indices = if let Some(field) = find_field(fields, "indices") {
        normalize_collection(field)?
            .iter()
            .map(parse_constr_from_sexp)
            .collect::<CoqImportResult<Vec<_>>>()?
    } else {
        Vec::new()
    };
    let motive = parse_constr_from_sexp(single_field_value(
        require_field(fields, "Case", "motive")?,
        "case motive",
    )?)?;
    let scrutinee = parse_constr_from_sexp(single_field_value(
        require_field(fields, "Case", "scrutinee")?,
        "case scrutinee",
    )?)?;
    let branches = normalize_collection(require_field(fields, "Case", "branches")?)?
        .iter()
        .map(parse_case_branch)
        .collect::<CoqImportResult<Vec<_>>>()?;

    Ok(Constr::Case(CaseInfo {
        inductive,
        universes,
        eliminator,
        parameters,
        indices,
        motive: Box::new(motive),
        scrutinee: Box::new(scrutinee),
        branches,
    }))
}

fn parse_case_branch(sexp: &Sexp) -> CoqImportResult<CaseBranch> {
    let items = expect_list(sexp, "case branch")?;
    if !head_is(items, "branch") {
        return Err(CoqImportError::UnexpectedToken {
            context: "case branch",
            token: head_atom(items, "case branch")?.to_string(),
        });
    }
    let fields = &items[1..];
    let constructor = if let Some(field) = find_field(fields, "constructor") {
        Some(parse_construct_ref(single_field_value(
            field,
            "branch constructor",
        )?)?)
    } else {
        None
    };
    let binders = if let Some(field) = find_field(fields, "binders") {
        normalize_collection(field)?
            .iter()
            .map(parse_binder)
            .collect::<CoqImportResult<Vec<_>>>()?
    } else {
        Vec::new()
    };
    let body = parse_constr_from_sexp(single_field_value(
        require_field(fields, "case branch", "body")?,
        "branch body",
    )?)?;

    Ok(CaseBranch {
        constructor,
        binders,
        body: Box::new(body),
    })
}

fn parse_fix(items: &[Sexp]) -> CoqImportResult<Constr> {
    Ok(Constr::Fix(parse_fix_term(items, "Fix")?))
}

fn parse_cofix(items: &[Sexp]) -> CoqImportResult<Constr> {
    Ok(Constr::CoFix(CoFixTerm {
        bodies: parse_fix_term(items, "CoFix")?.bodies,
        index: parse_fix_term(items, "CoFix")?.index,
    }))
}

fn parse_fix_term(items: &[Sexp], context: &'static str) -> CoqImportResult<FixTerm> {
    if has_any_field(&items[1..], &["index", "bodies"]) {
        let fields = &items[1..];
        return Ok(FixTerm {
            index: parse_usize(
                single_field_value(require_field(fields, context, "index")?, "fix index")?,
                "fix index",
            )?,
            bodies: normalize_collection(require_field(fields, context, "bodies")?)?
                .iter()
                .map(parse_fix_body)
                .collect::<CoqImportResult<Vec<_>>>()?,
        });
    }

    Ok(FixTerm {
        index: parse_usize(&items[1], "fix index")?,
        bodies: normalize_collection_from_item(&items[2])?
            .iter()
            .map(parse_fix_body)
            .collect::<CoqImportResult<Vec<_>>>()?,
    })
}

fn parse_fix_body(sexp: &Sexp) -> CoqImportResult<FixBody> {
    let items = expect_list(sexp, "fix body")?;
    if !head_is(items, "body") && !head_is(items, "fix_body") {
        return Err(CoqImportError::UnexpectedToken {
            context: "fix body",
            token: head_atom(items, "fix body")?.to_string(),
        });
    }
    let fields = &items[1..];
    let name = find_field(fields, "name")
        .map(|field| parse_optional_name(single_field_value(field, "fix body name")?))
        .transpose()?
        .flatten();
    let ty = parse_constr_from_sexp(single_field_value(
        require_field(fields, "fix body", "type")?,
        "fix body type",
    )?)?;
    let body = parse_constr_from_sexp(single_field_value(
        require_field(fields, "fix body", "body")?,
        "fix body term",
    )?)?;
    let recursive_arg = if let Some(field) = find_field(fields, "recursive_arg") {
        parse_u32(
            single_field_value(field, "recursive argument")?,
            "recursive argument",
        )?
    } else {
        0
    };

    Ok(FixBody {
        name,
        ty: Box::new(ty),
        body: Box::new(body),
        recursive_arg,
    })
}

fn parse_proj(items: &[Sexp]) -> CoqImportResult<Constr> {
    if has_any_field(&items[1..], &["inductive", "index", "name", "term"]) {
        let fields = &items[1..];
        return Ok(Constr::Proj {
            projection: ProjectionRef {
                inductive: parse_name(single_field_value(
                    require_field(fields, "Proj", "inductive")?,
                    "projection inductive",
                )?)?,
                projection_index: parse_u32(
                    single_field_value(
                        require_field(fields, "Proj", "index")?,
                        "projection index",
                    )?,
                    "projection index",
                )?,
                projection_name: find_field(fields, "name")
                    .map(|field| parse_optional_name(single_field_value(field, "projection name")?))
                    .transpose()?
                    .flatten(),
            },
            term: Box::new(parse_constr_from_sexp(single_field_value(
                require_field(fields, "Proj", "term")?,
                "projection term",
            )?)?),
        });
    }

    Ok(Constr::Proj {
        projection: ProjectionRef {
            inductive: parse_name(&items[1])?,
            projection_index: parse_u32(&items[2], "projection index")?,
            projection_name: None,
        },
        term: Box::new(parse_constr_from_sexp(&items[3])?),
    })
}

fn parse_construct_ref(sexp: &Sexp) -> CoqImportResult<ConstructRef> {
    match parse_constr_from_sexp(sexp)? {
        Constr::Construct(reference) => Ok(reference),
        _ => Err(CoqImportError::UnexpectedToken {
            context: "constructor reference",
            token: format!("{sexp:?}"),
        }),
    }
}

fn parse_binder(sexp: &Sexp) -> CoqImportResult<Binder> {
    let items = expect_list(sexp, "binder")?;
    if !head_is(items, "binder") {
        return Err(CoqImportError::UnexpectedToken {
            context: "binder",
            token: head_atom(items, "binder")?.to_string(),
        });
    }
    let rest = &items[1..];
    if has_any_field(rest, &["name", "info", "type"]) {
        let name = find_field(rest, "name")
            .map(|field| parse_optional_name(single_field_value(field, "binder name")?))
            .transpose()?
            .flatten();
        let info = if let Some(field) = find_field(rest, "info") {
            parse_binder_info(single_field_value(field, "binder info")?)?
        } else {
            CoqBinderKind::Default
        };
        let ty = parse_constr_from_sexp(single_field_value(
            require_field(rest, "binder", "type")?,
            "binder type",
        )?)?;
        return Ok(Binder {
            name,
            ty: Box::new(ty),
            info,
        });
    }

    let (name, info, ty) = match rest.len() {
        1 => (
            None,
            CoqBinderKind::Default,
            parse_constr_from_sexp(&rest[0])?,
        ),
        2 => (
            parse_optional_name(&rest[0])?,
            CoqBinderKind::Default,
            parse_constr_from_sexp(&rest[1])?,
        ),
        3 => (
            parse_optional_name(&rest[0])?,
            parse_binder_info(&rest[1])?,
            parse_constr_from_sexp(&rest[2])?,
        ),
        _ => {
            return Err(CoqImportError::UnexpectedToken {
                context: "binder",
                token: format!("{items:?}"),
            });
        }
    };
    Ok(Binder {
        name,
        ty: Box::new(ty),
        info,
    })
}

fn parse_sort(sexp: &Sexp) -> CoqImportResult<CoqSort> {
    match sexp {
        Sexp::Atom(atom) => parse_sort_atom(atom),
        Sexp::List(items) => {
            let head = head_atom(items, "sort")?;
            if head.eq_ignore_ascii_case("type") {
                return Ok(CoqSort::Type(parse_level(&items[1])?));
            }
            if head.eq_ignore_ascii_case("sort") {
                return parse_sort(&items[1]);
            }
            Err(CoqImportError::InvalidSort {
                sort: format!("{sexp:?}"),
            })
        }
    }
}

fn parse_sort_atom(atom: &str) -> CoqImportResult<CoqSort> {
    if atom.eq_ignore_ascii_case("prop") {
        Ok(CoqSort::Prop)
    } else if atom.eq_ignore_ascii_case("set") {
        Ok(CoqSort::Set)
    } else {
        Err(CoqImportError::InvalidSort {
            sort: atom.to_string(),
        })
    }
}

fn parse_level(sexp: &Sexp) -> CoqImportResult<UniverseLevel> {
    match sexp {
        Sexp::Atom(atom) => {
            if atom.eq_ignore_ascii_case("zero") {
                return Ok(UniverseLevel::Zero);
            }
            if let Ok(index) = atom.parse::<u32>() {
                return Ok(UniverseLevel::from_index(index));
            }
            Ok(UniverseLevel::Param(atom.clone()))
        }
        Sexp::List(items) => {
            let head = head_atom(items, "universe level")?;
            match head.to_ascii_lowercase().as_str() {
                "zero" => Ok(UniverseLevel::Zero),
                "succ" => Ok(UniverseLevel::Succ(Box::new(parse_level(&items[1])?))),
                "max" => {
                    let levels = items[1..]
                        .iter()
                        .map(parse_level)
                        .collect::<CoqImportResult<Vec<_>>>()?;
                    if levels.is_empty() {
                        return Err(CoqImportError::EmptyMaxUniverse);
                    }
                    Ok(UniverseLevel::Max(levels))
                }
                "imax" => Ok(UniverseLevel::IMax(
                    Box::new(parse_level(&items[1])?),
                    Box::new(parse_level(&items[2])?),
                )),
                "param" => Ok(UniverseLevel::Param(atom_string(
                    &items[1],
                    "universe parameter",
                )?)),
                _ => Err(CoqImportError::UnexpectedToken {
                    context: "universe level",
                    token: head.to_string(),
                }),
            }
        }
    }
}

fn parse_universe_instance(values: &[Sexp]) -> CoqImportResult<UniverseInstance> {
    Ok(UniverseInstance {
        levels: normalize_collection(values)?
            .iter()
            .map(parse_level)
            .collect::<CoqImportResult<Vec<_>>>()?,
    })
}

fn parse_universe_instance_from_item(item: &Sexp) -> CoqImportResult<UniverseInstance> {
    match item {
        Sexp::List(values) => Ok(UniverseInstance {
            levels: values
                .iter()
                .map(parse_level)
                .collect::<CoqImportResult<Vec<_>>>()?,
        }),
        _ => Ok(UniverseInstance {
            levels: vec![parse_level(item)?],
        }),
    }
}

fn parse_name(sexp: &Sexp) -> CoqImportResult<CoqName> {
    Ok(CoqName::from_dotted(&atom_string(sexp, "name")?))
}

fn parse_optional_name(sexp: &Sexp) -> CoqImportResult<Option<String>> {
    match sexp {
        Sexp::List(values) if values.is_empty() => Ok(None),
        Sexp::Atom(atom)
            if atom == "_"
                || atom.eq_ignore_ascii_case("anon")
                || atom.eq_ignore_ascii_case("anonymous")
                || atom.eq_ignore_ascii_case("none") =>
        {
            Ok(None)
        }
        _ => Ok(Some(atom_string(sexp, "optional name")?)),
    }
}

fn parse_string_list(values: &[Sexp]) -> CoqImportResult<Vec<String>> {
    normalize_collection(values)?
        .iter()
        .map(|item| atom_string(item, "string list item"))
        .collect()
}

fn parse_constant_decl_kind(sexp: &Sexp) -> CoqImportResult<ConstantDeclKind> {
    let kind = atom_string(sexp, "declaration kind")?;
    match kind.to_ascii_lowercase().as_str() {
        "axiom" => Ok(ConstantDeclKind::Axiom),
        "definition" | "constant" => Ok(ConstantDeclKind::Definition),
        "theorem" => Ok(ConstantDeclKind::Theorem),
        "opaque" => Ok(ConstantDeclKind::Opaque),
        _ => Err(CoqImportError::InvalidDeclarationKind { kind }),
    }
}

fn parse_inductive_kind(sexp: &Sexp) -> CoqImportResult<InductiveKind> {
    let kind = atom_string(sexp, "inductive kind")?;
    match kind.to_ascii_lowercase().as_str() {
        "inductive" => Ok(InductiveKind::Inductive),
        "coinductive" => Ok(InductiveKind::CoInductive),
        _ => Err(CoqImportError::InvalidInductiveKind { kind }),
    }
}

fn parse_binder_info(sexp: &Sexp) -> CoqImportResult<CoqBinderKind> {
    let info = atom_string(sexp, "binder info")?;
    match info.to_ascii_lowercase().as_str() {
        "default" | "explicit" => Ok(CoqBinderKind::Default),
        "implicit" => Ok(CoqBinderKind::Implicit),
        "strictimplicit" | "strict_implicit" => Ok(CoqBinderKind::StrictImplicit),
        "instimplicit" | "inst_implicit" | "instance" => Ok(CoqBinderKind::InstImplicit),
        _ => Err(CoqImportError::InvalidBinderInfo { info }),
    }
}

fn parse_cast_kind(sexp: &Sexp) -> CoqImportResult<CastKind> {
    let kind = atom_string(sexp, "cast kind")?;
    match kind.to_ascii_lowercase().as_str() {
        "default" => Ok(CastKind::Default),
        "vm" => Ok(CastKind::Vm),
        "native" => Ok(CastKind::Native),
        "revert" => Ok(CastKind::Revert),
        _ => Err(CoqImportError::InvalidCastKind { kind }),
    }
}

fn parse_u32(sexp: &Sexp, context: &'static str) -> CoqImportResult<u32> {
    let value = atom_string(sexp, context)?;
    value
        .parse::<u32>()
        .map_err(|_| CoqImportError::InvalidNumber { context, value })
}

fn parse_usize(sexp: &Sexp, context: &'static str) -> CoqImportResult<usize> {
    let value = atom_string(sexp, context)?;
    value
        .parse::<usize>()
        .map_err(|_| CoqImportError::InvalidNumber { context, value })
}

fn atom_string(sexp: &Sexp, context: &'static str) -> CoqImportResult<String> {
    Ok(expect_atom(sexp, context)?.to_string())
}

fn expect_atom<'a>(sexp: &'a Sexp, context: &'static str) -> CoqImportResult<&'a str> {
    match sexp {
        Sexp::Atom(atom) => Ok(atom.as_str()),
        Sexp::List(_) => Err(CoqImportError::ExpectedAtom { context }),
    }
}

fn expect_list<'a>(sexp: &'a Sexp, context: &'static str) -> CoqImportResult<&'a [Sexp]> {
    match sexp {
        Sexp::List(items) => Ok(items),
        Sexp::Atom(_) => Err(CoqImportError::ExpectedList { context }),
    }
}

fn head_atom<'a>(items: &'a [Sexp], context: &'static str) -> CoqImportResult<&'a str> {
    let Some(head) = items.first() else {
        return Err(CoqImportError::UnexpectedEof { context });
    };
    expect_atom(head, context)
}

fn head_is(items: &[Sexp], name: &str) -> bool {
    matches!(items.first(), Some(Sexp::Atom(atom)) if atom.eq_ignore_ascii_case(name))
}

fn is_declaration_form(sexp: &Sexp) -> bool {
    match sexp {
        Sexp::List(items) if !items.is_empty() => matches!(
            head_atom(items, "declaration head"),
            Ok(head)
                if head.eq_ignore_ascii_case("constant")
                    || head.eq_ignore_ascii_case("definition")
                    || head.eq_ignore_ascii_case("axiom")
                    || head.eq_ignore_ascii_case("theorem")
                    || head.eq_ignore_ascii_case("opaque")
                    || head.eq_ignore_ascii_case("inductive")
                    || head.eq_ignore_ascii_case("coinductive")
        ),
        _ => false,
    }
}

fn find_field<'a>(items: &'a [Sexp], name: &str) -> Option<&'a [Sexp]> {
    items.iter().find_map(|item| match item {
        Sexp::List(values)
            if !values.is_empty()
                && matches!(&values[0], Sexp::Atom(atom) if atom.eq_ignore_ascii_case(name)) =>
        {
            Some(&values[1..])
        }
        _ => None,
    })
}

fn find_field_any<'a>(items: &'a [Sexp], names: &[&str]) -> Option<&'a [Sexp]> {
    names.iter().find_map(|name| find_field(items, name))
}

fn require_field<'a>(
    items: &'a [Sexp],
    context: &'static str,
    field: &'static str,
) -> CoqImportResult<&'a [Sexp]> {
    find_field(items, field).ok_or(CoqImportError::MissingField { context, field })
}

fn single_field_value<'a>(values: &'a [Sexp], context: &'static str) -> CoqImportResult<&'a Sexp> {
    if values.len() != 1 {
        return Err(CoqImportError::UnexpectedToken {
            context,
            token: format!("{values:?}"),
        });
    }
    Ok(&values[0])
}

fn has_any_field(items: &[Sexp], names: &[&str]) -> bool {
    find_field_any(items, names).is_some()
}

fn normalize_collection(values: &[Sexp]) -> CoqImportResult<&[Sexp]> {
    if values.len() == 1 {
        if let Sexp::List(items) = &values[0] {
            return Ok(items);
        }
    }
    Ok(values)
}

fn normalize_collection_from_item(item: &Sexp) -> CoqImportResult<&[Sexp]> {
    match item {
        Sexp::List(items) => Ok(items),
        _ => Err(CoqImportError::ExpectedList {
            context: "collection",
        }),
    }
}

struct Parser<'a> {
    input: &'a str,
    offset: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, offset: 0 }
    }

    fn is_eof(&self) -> bool {
        self.offset >= self.input.len()
    }

    fn skip_ws_and_comments(&mut self) {
        loop {
            let remainder = &self.input[self.offset..];
            let before = self.offset;
            let trimmed = remainder.trim_start_matches(char::is_whitespace);
            self.offset += remainder.len() - trimmed.len();
            if self.peek_char() == Some(';') {
                while let Some(ch) = self.bump_char() {
                    if ch == '\n' {
                        break;
                    }
                }
                continue;
            }
            if self.offset == before {
                break;
            }
        }
    }

    fn parse_expr(&mut self, context: &'static str) -> CoqImportResult<Sexp> {
        self.skip_ws_and_comments();
        match self.peek_char() {
            None => Err(CoqImportError::UnexpectedEof { context }),
            Some('(') => self.parse_list(context),
            Some('"') => self.parse_string(),
            Some(')') => Err(CoqImportError::UnexpectedToken {
                context,
                token: ")".to_string(),
            }),
            Some(_) => self.parse_atom(context),
        }
    }

    fn parse_list(&mut self, context: &'static str) -> CoqImportResult<Sexp> {
        self.bump_char();
        let mut items = Vec::new();
        loop {
            self.skip_ws_and_comments();
            match self.peek_char() {
                None => return Err(CoqImportError::UnexpectedEof { context }),
                Some(')') => {
                    self.bump_char();
                    return Ok(Sexp::List(items));
                }
                _ => items.push(self.parse_expr(context)?),
            }
        }
    }

    fn parse_string(&mut self) -> CoqImportResult<Sexp> {
        self.bump_char();
        let mut out = String::new();
        loop {
            let Some(ch) = self.bump_char() else {
                return Err(CoqImportError::UnexpectedEof { context: "string" });
            };
            match ch {
                '"' => return Ok(Sexp::Atom(out)),
                '\\' => {
                    let Some(escaped) = self.bump_char() else {
                        return Err(CoqImportError::UnexpectedEof {
                            context: "string escape",
                        });
                    };
                    let translated = match escaped {
                        '"' => '"',
                        '\\' => '\\',
                        'n' => '\n',
                        'r' => '\r',
                        't' => '\t',
                        other => other,
                    };
                    out.push(translated);
                }
                other => out.push(other),
            }
        }
    }

    fn parse_atom(&mut self, context: &'static str) -> CoqImportResult<Sexp> {
        let start = self.offset;
        while let Some(ch) = self.peek_char() {
            if ch.is_whitespace() || ch == '(' || ch == ')' || ch == ';' {
                break;
            }
            self.bump_char();
        }
        if self.offset == start {
            return Err(CoqImportError::UnexpectedToken {
                context,
                token: self.peek_char().unwrap_or('\0').to_string(),
            });
        }
        Ok(Sexp::Atom(self.input[start..self.offset].to_string()))
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.offset..].chars().next()
    }

    fn bump_char(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.offset += ch.len_utf8();
        Some(ch)
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Specialize the imported IO.Error.toString on every constructor. Constructor
//! fields stay symbolic. Only the String and UInt32 operations below survive
//! reduction, so the driver can print the exact selected equation.

use anyhow::{anyhow, bail, ensure, Result};
use clean_compiler::{ir::IRType, to_ir::build_ctor_env};
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Level, Literal, Name, TypeChecker};
use std::fmt::Write;

#[derive(Debug)]
pub(super) struct ErrorPrinter(String);

#[derive(Clone, Copy, PartialEq, Eq)]
enum Field {
    Text,
    File,
    Code,
}

impl ErrorPrinter {
    pub(super) fn definition(&self) -> &str {
        &self.0
    }

    pub(super) fn check(env: &Environment) -> Result<Self> {
        let family_name = Name::interned("IO.Error");
        let formatter = Name::interned("IO.Error.toString");
        let string = Expr::const_str("String");
        let family = env
            .get_inductive(&family_name)
            .ok_or_else(|| anyhow!("missing IO.Error family"))?;
        ensure!(
            super::state_entry::imported(env, "IO.Error", "Init.System.IOError")
                && super::state_entry::imported(env, "IO.Error.toString", "Init.System.IOError")
                && family.num_params == 0
                && family.num_indices == 0
                && !family.constructor_names.is_empty()
                && family.constructor_names.len() <= 256
                && env.get_const(&formatter).is_some_and(|i| i.type_
                    == Expr::arrow(Expr::const_str("IO.Error"), string.clone())
                    && i.value.is_some()),
            "invalid stable IO.Error family or formatter"
        );
        ensure!(
            hash_hex(&env.closure_digest(&formatter)?)
                == "e4f9802686f47eb35db855b193732f655a51713ef47b9cfed85f146c203f8a2a",
            "stable IO.Error.toString or its transitive source declarations changed"
        );
        check_operations(env)?;
        check_option_layout(env)?;
        let reduced = formatter_environment(env, &formatter)?;
        let tc = TypeChecker::new(&reduced);
        let mut out = String::from(include_str!("native_io_error.c"));
        out.push_str("\nstatic bool clean_driver_report_error(clean_obj* error) {\n  if (!error) return false;\n  switch (clean_obj_tag(error)) {\n");
        for (tag, name) in family.constructor_names.iter().enumerate() {
            let fields = checked_fields(env, name, tag)?;
            emit_field_reads(&mut out, tag, &fields)?;
            out.push_str(
                "      bool stopped = false;\n      fputs(\"uncaught exception: \", stderr);\n",
            );
            emit_equations(&tc, &formatter, name, &fields, &mut out)?;
            out.push_str("      fputc('\\n', stderr);\n      return true;\n    }\n");
        }
        out.push_str("    default: return false;\n  }\n}\n");
        Ok(Self(out))
    }
}

fn check_option_layout(env: &Environment) -> Result<()> {
    let option_name = Name::interned("Option");
    let option_info = env
        .get_inductive(&option_name)
        .ok_or_else(|| anyhow!("missing Option family"))?;
    ensure!(
        super::state_entry::imported(env, "Option", "Init.Prelude")
            && option_info.constructor_names
                == [Name::interned("Option.none"), Name::interned("Option.some")]
            && option_info.num_params == 1
            && option_info.num_indices == 0,
        "unsupported Option layout for IO.Error"
    );
    for (index, ctor) in option_info.constructor_names.iter().enumerate() {
        let c = env
            .get_constructor(ctor)
            .ok_or_else(|| anyhow!("missing {ctor}"))?;
        ensure!(
            super::state_entry::imported(env, &ctor.to_string(), "Init.Prelude")
                && c.inductive_name == option_name
                && c.num_params == 1
                && c.num_fields == index as u32
                && c.constructor_idx == index as u32,
            "unsupported Option constructor layout for IO.Error"
        );
    }

    Ok(())
}

fn formatter_environment(env: &Environment, formatter: &Name) -> Result<Environment> {
    // A formatter may reduce only through ordinary declarations. Stop at
    // executable overrides and operations carried by this driver.
    let mut reduced = env.clone();
    for name in env.dependency_closure(formatter)? {
        let substituted = env.is_extern(&name)
            || env.has_implemented_by(&name)
            || env.is_unsafe(&name)
            || env.is_partial(&name)
            || env.is_noncomputable(&name);
        let rules = clean_kernel::env::csimp::rules_for(env, Some(&name));
        let replaced_reference = !rules.is_empty()
            && env
                .get_const(&name)
                .and_then(|c| c.value.as_ref())
                .is_some_and(|body| {
                    let mut used = std::collections::HashSet::new();
                    body.used_constants_dag(
                        clean_kernel::expr::UsedConstants::WithProjectionStructures,
                        &mut used,
                    );
                    rules.iter().any(|r| used.contains(&r.from))
                });
        if substituted || replaced_reference {
            reduced.forget_decl(&name);
        }
    }
    for name in ["String.append", "Char.toLower", "Nat.repr", "UInt32.toNat"] {
        reduced.forget_decl(&Name::interned(name));
    }
    Ok(reduced)
}

fn checked_fields(env: &Environment, name: &Name, tag: usize) -> Result<Vec<Field>> {
    let string = Expr::const_str("String");
    let option = Expr::app(
        Expr::const_str_levels("Option", vec![Level::zero()]),
        string.clone(),
    );
    let uint32 = Expr::const_str("UInt32");
    let ctor = env
        .get_constructor(name)
        .ok_or_else(|| anyhow!("missing IO.Error constructor {name}"))?;
    ensure!(
        super::state_entry::imported(env, &name.to_string(), "Init.System.IOError")
            && ctor.inductive_name == Name::interned("IO.Error")
            && ctor.num_params == 0
            && ctor.constructor_idx == tag as u32
            && ctor.level_params.is_empty(),
        "invalid stable IO.Error constructor {name}"
    );
    let mut fields = Vec::new();
    let mut ty = &ctor.type_;
    while let ExprKind::Pi(_, domain, result) = ty.kind() {
        fields.push(if **domain == string {
            Field::Text
        } else if **domain == uint32 {
            Field::Code
        } else if **domain == option {
            Field::File
        } else {
            bail!("unsupported field of IO.Error constructor {name}")
        });
        ty = result;
    }
    ensure!(
        fields.len() == ctor.num_fields as usize && *ty == Expr::const_str("IO.Error"),
        "invalid IO.Error constructor type {name}"
    );
    let (metadata, _) = build_ctor_env(&[ctor])?;
    let meta = &metadata[name];
    let objects = fields.iter().filter(|f| **f != Field::Code).count();
    let codes = fields.len() - objects;
    ensure!(
        codes <= 1
            && fields.iter().filter(|f| **f == Field::File).count() <= 1
            && meta.tag == tag as u32
            && meta.num_objects == objects as u32
            && meta.num_scalars == codes as u32
            && meta.field_types.len() == fields.len()
            && meta
                .field_types
                .iter()
                .zip(&fields)
                .all(|(ty, field)| match field {
                    Field::Code => *ty == IRType::UInt32,
                    _ => ty.is_object(),
                }),
        "unsupported emitted IO.Error layout for {name}"
    );
    Ok(fields)
}

/// Constructor layout and tags consumed by the stable C runtime errno decoder.
pub(super) fn stdout_error_tags(env: &Environment) -> Result<String> {
    check_option_layout(env)?;
    let mut code =
        String::from("#include <errno.h>\n#include <stdio.h>\n#include \"clean_runtime.h\"\n");
    for (tag, (short, macro_name)) in [
        ("alreadyExists", "ALREADY_EXISTS"),
        ("otherError", "OTHER_ERROR"),
        ("resourceBusy", "RESOURCE_BUSY"),
        ("resourceVanished", "RESOURCE_VANISHED"),
        ("unsupportedOperation", "UNSUPPORTED_OPERATION"),
        ("hardwareFault", "HARDWARE_FAULT"),
        ("unsatisfiedConstraints", "UNSATISFIED_CONSTRAINTS"),
        ("illegalOperation", "ILLEGAL_OPERATION"),
        ("protocolError", "PROTOCOL_ERROR"),
        ("timeExpired", "TIME_EXPIRED"),
        ("interrupted", "INTERRUPTED"),
        ("noFileOrDirectory", "NO_FILE_OR_DIRECTORY"),
        ("invalidArgument", "INVALID_ARGUMENT"),
        ("permissionDenied", "PERMISSION_DENIED"),
        ("resourceExhausted", "RESOURCE_EXHAUSTED"),
        ("inappropriateType", "INAPPROPRIATE_TYPE"),
        ("noSuchThing", "NO_SUCH_THING"),
    ]
    .iter()
    .enumerate()
    {
        let name = Name::from_string(&format!("IO.Error.{short}"));
        let fields = checked_fields(env, &name, tag)?;
        let expected: &[Field] = match *short {
            "alreadyExists" | "invalidArgument" | "permissionDenied" | "resourceExhausted"
            | "inappropriateType" | "noSuchThing" => &[Field::File, Field::Code, Field::Text],
            "interrupted" | "noFileOrDirectory" => &[Field::Text, Field::Code, Field::Text],
            _ => &[Field::Code, Field::Text],
        };
        ensure!(
            fields == expected,
            "unsupported stdout error fields for {name}"
        );
        writeln!(code, "#define CLEAN_STDIO_{macro_name} {tag}")?;
    }
    Ok(code)
}

fn emit_field_reads(out: &mut String, tag: usize, fields: &[Field]) -> Result<()> {
    let objects = fields.iter().filter(|f| **f != Field::Code).count();
    let bytes = (fields.len() - objects) * std::mem::size_of::<u32>();
    writeln!(out, "    case {tag}: {{")?;
    if fields.is_empty() {
        writeln!(out, "      if (error != clean_box({tag})) return false;")?;
    } else {
        writeln!(
            out,
            "      if (!clean_driver_error_ctor(error, {tag}, {objects}, {bytes})) return false;"
        )?;
    }
    let mut object_slot = 0;
    for (i, field) in fields.iter().enumerate() {
        match field {
            Field::Code => {
                writeln!(out,"      uint32_t code{i} = clean_ctor_get_uint32(error, {objects} * sizeof(clean_obj*));")?;
            }
            Field::Text | Field::File => {
                writeln!(
                    out,
                    "      clean_obj* text{i} = clean_ctor_get(error, {object_slot});"
                )?;
                object_slot += 1;
                if *field == Field::File {
                    writeln!(
                        out,
                        "      if (!clean_driver_optional_text(&text{i})) return false;"
                    )?;
                } else {
                    writeln!(
                        out,
                        "      if (!clean_driver_is_text(text{i})) return false;"
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn emit_equations(
    tc: &TypeChecker<'_>,
    formatter: &Name,
    name: &Name,
    fields: &[Field],
    out: &mut String,
) -> Result<()> {
    let string = Expr::const_str("String");
    let optional = fields.iter().position(|f| *f == Field::File);
    for present in [false, true] {
        if present && optional.is_none() {
            break;
        }
        let mut args = Vec::new();
        for (i, f) in fields.iter().enumerate() {
            let value = Expr::fvar(FVarId::new(i as u64));
            args.push(if *f != Field::File {
                value
            } else if present {
                Expr::apps(
                    Expr::const_str_levels("Option.some", vec![Level::zero()]),
                    [string.clone(), value],
                )
            } else {
                Expr::app(
                    Expr::const_str_levels("Option.none", vec![Level::zero()]),
                    string.clone(),
                )
            });
        }
        let expr = Expr::app(
            Expr::const_(formatter.clone(), vec![]),
            Expr::apps(Expr::const_(name.clone(), vec![]), args),
        );
        if let Some(slot) = optional {
            if !present {
                writeln!(out, "      if (!text{slot}) {{")?;
            } else {
                out.push_str("      } else {\n");
            }
        }
        emit_string(tc, &expr, fields, present, false, 0, out)?;
    }
    if optional.is_some() {
        out.push_str("      }\n");
    }
    Ok(())
}

fn emit_string(
    tc: &TypeChecker<'_>,
    expr: &Expr,
    fields: &[Field],
    file: bool,
    lower: bool,
    depth: usize,
    out: &mut String,
) -> Result<()> {
    ensure!(
        depth < 32,
        "stable IO.Error formatter expression is too deep"
    );
    let result = tc.whnf(expr);
    match result.kind() {
        ExprKind::Lit(Literal::String(text)) => {
            let data = text.as_bytes();
            let mut literal = String::new();
            for b in data {
                write!(literal, "\\x{b:02x}")?;
            }
            writeln!(
                out,
                "        clean_driver_emit_bytes(&stopped, \"{literal}\", {}, {});",
                data.len(),
                u8::from(lower)
            )?;
        }
        ExprKind::FVar(var) => {
            let slot = usize::try_from(var.as_u64())?;
            ensure!(
                fields
                    .get(slot)
                    .is_some_and(|f| *f == Field::Text || (*f == Field::File && file)),
                "formatter expects a different IO.Error string field"
            );
            writeln!(out,"        clean_driver_emit_bytes(&stopped, clean_string_data(text{slot}), clean_string_len(text{slot}), {});",u8::from(lower))?;
        }
        _ => {
            let ExprKind::Const(name, _) = result.get_app_fn().kind() else {
                bail!("unsupported IO.Error formatter expression")
            };
            let args = result.get_app_args();
            match (name.to_string().as_str(), args.as_slice()) {
                ("String.append", [a, b]) if !lower => {
                    emit_string(tc, a, fields, file, false, depth + 1, out)?;
                    emit_string(tc, b, fields, file, false, depth + 1, out)?;
                }
                ("String.Pos.Raw.set", [text, pos, character]) => {
                    // The SDK's decapitalize sets position zero in the same string
                    // to the lower-case form of the character read at zero. Both
                    // position operations are genuine registered runtime externs.
                    let zero = Expr::app(Expr::const_str("String.Pos.Raw.mk"), Expr::nat_lit(0));
                    let get = Expr::apps(
                        Expr::const_str("String.Pos.Raw.get"),
                        [(*text).clone(), zero.clone()],
                    );
                    let lowered = Expr::app(Expr::const_str("Char.toLower"), get);
                    ensure!(
                        tc.is_def_eq(pos, &zero) && tc.is_def_eq(character, &lowered),
                        "unsupported string update in stable IO error formatter"
                    );
                    emit_string(tc, text, fields, file, true, depth + 1, out)?
                }
                ("Nat.repr", [n]) if !lower => {
                    let n = tc.whnf(n);
                    let a = n.get_app_args();
                    ensure!(
                        matches!(n.get_app_fn().kind(),ExprKind::Const(name,_) if name==&Name::interned("UInt32.toNat"))
                            && a.len() == 1,
                        "formatter expects a different numeric carrier"
                    );
                    let value = tc.whnf(a[0]);
                    let ExprKind::FVar(v) = value.kind() else {
                        bail!("numeric formatter has no IO.Error field")
                    };
                    let slot = usize::try_from(v.as_u64())?;
                    ensure!(
                        fields.get(slot) == Some(&Field::Code),
                        "formatter expects a different IO.Error status field"
                    );
                    writeln!(
                        out,
                        "        clean_driver_error_code(&stopped, code{slot});"
                    )?;
                }
                _ => bail!("unsupported operation {name} in the stable IO.Error formatter"),
            }
        }
    }
    Ok(())
}

/// The C leaves implement operations from the official 4.36.0
/// SDK. Bind each leaf to its decoded transitive kernel records and its selected
/// compiler implementation before using a host operation for it.
fn check_operations(env: &Environment) -> Result<()> {
    use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
    // The independently replayed stable_io_error_uint32 proofs establish
    // both the logical and selected Nat.reprFast equation for every UInt32.
    // Bind their target operations and platform width to this SDK as well.
    for (name, owner, symbol, digest, domain, range) in [
        (
            "UInt32.toUSize",
            "Init.Data.UInt.Basic",
            "lean_uint32_to_usize",
            "7a4318267acdd8c7abe2862047c03593f9d4301b6653b3e894d2753e68fa78d8",
            "UInt32",
            "USize",
        ),
        (
            "USize.repr",
            "Init.Data.Repr",
            "lean_string_of_usize",
            "27cc611b8ff922dbb6315d794f38b47ac0870e71e851f320d3187ded96d0c6f1",
            "USize",
            "String",
        ),
    ] {
        let name = Name::interned(name);
        ensure!(
            clean_olean::import::lean_declaration_artifact(env, &name).as_deref() == Some(owner)
                && !env.is_unsafe(&name)
                && !env.is_partial(&name)
                && !env.is_noncomputable(&name)
                && !env.has_implemented_by(&name)
                && env.get_const(&name).is_some_and(
                    |i| i.type_ == Expr::arrow(Expr::const_str(domain), Expr::const_str(range))
                )
                && hash_hex(&env.closure_digest(&name)?) == digest
                && matches!(env.extern_metadata(&name)?,Some(CompilerExternMetadata::Complete(b)) if b.arity==CompilerExternArity::Unspecified &&
                matches!(b.entries.as_slice(), [CompilerExternEntry::Standard{backend,symbol:found}] if *backend==Name::interned("all") && found==symbol)),
            "invalid bounded decimal word operation {name}"
        );
    }
    let width = Name::interned("System.Platform.numBits");
    let query = Name::interned("System.Platform.getNumBits");
    ensure!(
        super::state_entry::imported(env, "System.Platform.numBits", "Init.Prelude")
            && hash_hex(&env.closure_digest(&width)?)
                == "b77a4cd4a43609e792b687c3541b5388306c9ce86298b7f871d85864b3f1bdc0"
            && clean_olean::import::lean_declaration_artifact(env, &query).as_deref()
                == Some("Init.Prelude")
            && !env.has_implemented_by(&query)
            && !env.is_unsafe(&query)
            && !env.is_partial(&query)
            && !env.is_noncomputable(&query)
            && matches!(env.extern_metadata(&query)?,Some(CompilerExternMetadata::Complete(b)) if b.arity==CompilerExternArity::Unspecified &&
            matches!(b.entries.as_slice(),[CompilerExternEntry::Standard{backend,symbol}] if *backend==Name::interned("all") && symbol=="lean_system_platform_nbits")),
        "invalid SDK word-width query for bounded IO error codes"
    );
    let leaves = [
        (
            "String.append",
            "Init.Data.String.Defs",
            Some("lean_string_append"),
        ),
        ("String.decapitalize", "Init.Data.String.Modify", None),
        (
            "String.Pos.Raw.get",
            "Init.Data.String.Basic",
            Some("lean_string_utf8_get"),
        ),
        (
            "String.Pos.Raw.set",
            "Init.Data.String.Modify",
            Some("lean_string_utf8_set"),
        ),
        ("Char.toLower", "Init.Data.Char.Basic", None),
        ("Nat.repr", "Init.Data.Repr", None),
        ("Nat.reprFast", "Init.Data.Repr", None),
        ("UInt32.toNat", "Init.Prelude", Some("lean_uint32_to_nat")),
    ];
    for (name, module, external) in leaves {
        let id = Name::interned(name);
        let info = env
            .get_const(&id)
            .ok_or_else(|| anyhow!("missing stable formatting leaf {name}"))?;
        ensure!(
            clean_olean::import::lean_declaration_artifact(env, &id).as_deref() == Some(module)
                && !env.is_unsafe(&id)
                && !env.is_partial(&id)
                && !env.is_noncomputable(&id)
                && info.value.is_some(),
            "invalid stable error formatting leaf {name}"
        );
        let implementation = (name == "Nat.repr").then(|| Name::interned("Nat.reprFast"));
        ensure!(
            env.get_implemented_by(&id) == implementation.as_ref(),
            "incompatible runtime implementation for {name}"
        );
        if name == "UInt32.toNat" {
            ensure!(
                crate::native_ffi_audit::select_stable_uint32_shim(env, info)?.is_some(),
                "missing checked UInt32.toNat binding"
            );
        } else if let Some(symbol) = external {
            let Some(CompilerExternMetadata::Complete(descriptor)) = env.extern_metadata(&id)?
            else {
                bail!("missing complete {name} extern descriptor")
            };
            ensure!(
                descriptor.arity == CompilerExternArity::Unspecified
                    && matches!(descriptor.entries.as_slice(),[CompilerExternEntry::Standard{backend,symbol:actual}] if *backend==Name::interned("all") && actual==symbol),
                "incompatible {name} extern binding"
            );
        } else {
            ensure!(
                !env.is_extern(&id) && env.extern_metadata(&id)?.is_none(),
                "foreign implementation for {name}"
            );
        }
    }
    let position = Name::interned("String.Pos.Raw.mk");
    ensure!(
        super::state_entry::imported(env, "String.Pos.Raw.mk", "Init.Prelude")
            && env.get_constructor(&position).is_some_and(|c| c.type_
                == Expr::arrow(Expr::const_str("Nat"), Expr::const_str("String.Pos.Raw"))
                && c.num_params == 0
                && c.num_fields == 1
                && c.constructor_idx == 0),
        "incompatible stable String.Pos.Raw constructor"
    );
    let roots = ["Char.toLower", "Nat.repr", "Nat.reprFast"].map(Name::interned);
    let checked = clean_compiler::RuntimeBindingClosure::check_executable(env, &roots)?;
    // All 268 selected body/constructor/extern rows, including nested compiler
    // overrides. The byte bound also refuses a larger replacement transcript.
    let mut bytes = vec![0u8; 28239];
    let mut destination = bytes.as_mut_slice();
    serde_json::to_writer(&mut destination, &checked.selected_binding_records())?;
    use sha2::{Digest, Sha256};
    ensure!(
        destination.is_empty()
            && hash_hex(&Sha256::digest(&bytes).into())
                == "5a14b719b41538908086592bc19c9f501800ab2ba65c62327d78c06c4ea784e4",
        "the selected native implementation of a stable error formatting primitive changed"
    );
    Ok(())
}

fn hash_hex(value: &[u8; 32]) -> String {
    value.iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
#[path = "native_io_error_proof_tests.rs"]
mod proof_tests;

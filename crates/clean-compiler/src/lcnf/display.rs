// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::fmt;

// ════════════════════════════════════════════════════════════════════════════
// Display implementations for debugging
// ════════════════════════════════════════════════════════════════════════════

impl fmt::Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Arg::Erased => write!(f, "◇"),
            Arg::FVar(id) => write!(f, "_x{}", id.as_u64()),
            Arg::Type(e) => write!(f, "@{e:?}"),
            Arg::Index(idx) => write!(f, "#{idx}"),
        }
    }
}

impl fmt::Display for LetValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LetValue::Lit(Literal::Nat(n)) => write!(f, "{n}"),
            LetValue::Lit(Literal::String(s)) => write!(f, "\"{s}\""),
            LetValue::Erased => write!(f, "◇"),
            LetValue::Proj {
                type_name,
                idx,
                structure,
            } => {
                write!(f, "{type_name}.{idx} _x{}", structure.as_u64())
            }
            LetValue::Const { name, args, .. } => {
                write!(f, "{name}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                Ok(())
            }
            LetValue::FVar { fvar, args } => {
                write!(f, "_x{}", fvar.as_u64())?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                Ok(())
            }
            LetValue::Ctor { name, args, .. } => {
                write!(f, "{name}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                Ok(())
            }
            LetValue::Reuse {
                slot,
                ctor_name,
                args,
                ..
            } => {
                write!(f, "_reuse _x{} {ctor_name}", slot.as_u64())?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_code(f, self, 0)
    }
}

fn write_code(f: &mut fmt::Formatter<'_>, code: &Code, indent: usize) -> fmt::Result {
    let pad = "  ".repeat(indent);
    match code {
        Code::Let(decl, body) => {
            writeln!(f, "{pad}let _x{} := {}", decl.fvar_id.as_u64(), decl.value)?;
            write_code(f, body, indent)
        }
        Code::Fun(decl, body) => {
            write!(f, "{pad}fun _x{} (", decl.fvar_id.as_u64())?;
            for (i, p) in decl.params.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "_x{}", p.fvar_id.as_u64())?;
            }
            writeln!(f, ") :=")?;
            write_code(f, &decl.body, indent + 1)?;
            write_code(f, body, indent)
        }
        Code::JoinPoint(decl, body) => {
            write!(f, "{pad}jp _x{} (", decl.fvar_id.as_u64())?;
            for (i, p) in decl.params.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "_x{}", p.fvar_id.as_u64())?;
            }
            writeln!(f, ") :=")?;
            write_code(f, &decl.body, indent + 1)?;
            write_code(f, body, indent)
        }
        Code::Cases(cases) => {
            writeln!(f, "{pad}cases _x{} of", cases.scrutinee.as_u64())?;
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => {
                        write!(f, "{pad}| {ctor_name}")?;
                        for p in params {
                            write!(f, " _x{}", p.fvar_id.as_u64())?;
                        }
                        writeln!(f, " =>")?;
                        write_code(f, body, indent + 1)?;
                    }
                    Alt::Default(body) => {
                        writeln!(f, "{pad}| _ =>")?;
                        write_code(f, body, indent + 1)?;
                    }
                }
            }
            Ok(())
        }
        Code::Jmp { jp, args } => {
            write!(f, "{pad}jmp _x{}", jp.as_u64())?;
            for arg in args {
                write!(f, " {arg}")?;
            }
            writeln!(f)
        }
        Code::Return(fvar) => writeln!(f, "{pad}return _x{}", fvar.as_u64()),
        Code::Unreachable(_) => writeln!(f, "{pad}unreachable"),
    }
}

impl fmt::Display for Decl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "def {} (", self.name)?;
        for (i, p) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "_x{}", p.fvar_id.as_u64())?;
        }
        writeln!(f, ") :=")?;
        match &self.body {
            DeclValue::Code(code) => write_code(f, code, 1),
            DeclValue::Extern(attr) => {
                write!(f, "  extern")?;
                for e in &attr.entries {
                    write!(f, " [{}:{}]", e.backend, e.name)?;
                }
                writeln!(f)
            }
        }
    }
}

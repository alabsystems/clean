// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's own text rendering of IR declarations, ported so a decoded
//! declaration can be compared with what the pinned toolchain prints
//! (`clean olean ir-census` and tests). Names render through
//! [`name_to_string`].
//!
//! [`format_decl`] is `Lean.IR.formatDecl` (`Lean/Compiler/IR/Format.lean`)
//! followed by `Format.pretty`. Every `Format.line` in that file sits outside
//! any `group`, so the layout is exactly "newline plus the current `nest`
//! indentation"; the only groups (`Format.bracket`/`sbracket`) contain no line
//! breaks. No width decision is involved. A newline inside a text (a name
//! component) breaks the same way (`Layout::text`).

use super::format::{name_to_string, nat_to_string};
use super::types::{
    Alt, Arg, CtorInfo, Decl, Expr, FnBody, Instr, IrType, LitVal, Param, Terminal,
};

// --- literal rendering -------------------------------------------------------

/// `String.quote` (`Init/Data/Repr.lean`, `Char.quoteCore (inString := true)`).
#[must_use]
pub(crate) fn quote_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            c if u32::from(c) <= 31 || c == '\x7f' => {
                out.push_str(&format!("\\x{:02x}", u32::from(c)));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// --- IR formatting -----------------------------------------------------------

fn fmt_type(t: &IrType) -> String {
    match t {
        IrType::Float => "float".into(),
        IrType::Float32 => "float32".into(),
        IrType::UInt8 => "u8".into(),
        IrType::UInt16 => "u16".into(),
        IrType::UInt32 => "u32".into(),
        IrType::UInt64 => "u64".into(),
        IrType::USize => "usize".into(),
        IrType::Erased => "◾".into(),
        IrType::Void => "void".into(),
        IrType::Object => "obj".into(),
        IrType::Tagged => "tagged".into(),
        IrType::TObject => "tobj".into(),
        IrType::Struct { types, .. } => format!("struct {{{}}}", join_types(types)),
        IrType::Union { types, .. } => format!("union {{{}}}", join_types(types)),
    }
}

fn join_types(types: &[IrType]) -> String {
    types.iter().map(fmt_type).collect::<Vec<_>>().join(", ")
}

fn fmt_arg(a: &Arg) -> String {
    match a {
        Arg::Var(x) => format!("x_{}", x.0),
        Arg::Erased => "◾".into(),
    }
}

/// `formatArray`: each element preceded by a space.
fn fmt_args(args: &[Arg]) -> String {
    args.iter().map(|a| format!(" {}", fmt_arg(a))).collect()
}

fn fmt_ctor_info(i: &CtorInfo) -> String {
    let mut r = format!("ctor_{}", i.cidx);
    if i.usize > 0 || i.ssize > 0 {
        r.push_str(&format!(".{}.{}", i.usize, i.ssize));
    }
    if !i.name.is_anon() {
        r.push_str(&format!("[{}]", name_to_string(&i.name)));
    }
    r
}

fn fmt_expr(e: &Expr) -> String {
    match e {
        Expr::Ctor { info, args } => format!("{}{}", fmt_ctor_info(info), fmt_args(args)),
        Expr::Reset { n, x } => format!("reset[{n}] x_{}", x.0),
        Expr::Reuse {
            x,
            info,
            update_header,
            args,
        } => format!(
            "reuse{} x_{} in {}{}",
            if *update_header { "!" } else { "" },
            x.0,
            fmt_ctor_info(info),
            fmt_args(args)
        ),
        Expr::Proj { i, x } => format!("proj[{i}] x_{}", x.0),
        Expr::UProj { i, x } => format!("uproj[{i}] x_{}", x.0),
        Expr::SProj { n, offset, x } => format!("sproj[{n}, {offset}] x_{}", x.0),
        Expr::Fap { f, args } => format!("{}{}", name_to_string(f), fmt_args(args)),
        Expr::Pap { f, args } => format!("pap {}{}", name_to_string(f), fmt_args(args)),
        Expr::Ap { x, args } => format!("app x_{}{}", x.0, fmt_args(args)),
        Expr::Box { x, .. } => format!("box x_{}", x.0),
        Expr::Unbox { x } => format!("unbox x_{}", x.0),
        Expr::Lit(LitVal::Num(v)) => nat_to_string(v.limbs()),
        Expr::Lit(LitVal::Str(s)) => quote_string(s),
        Expr::IsShared { x } => format!("isShared x_{}", x.0),
    }
}

fn fmt_param(p: &Param) -> String {
    format!(
        "(x_{} : {}{})",
        p.x.0,
        if p.borrow { "@& " } else { "" },
        fmt_type(&p.ty)
    )
}

fn fmt_params(ps: &[Param]) -> String {
    ps.iter().map(|p| format!(" {}", fmt_param(p))).collect()
}

/// A `Format` renderer restricted to what `Format.lean` builds: text,
/// `line` (newline + current indentation) and `nest`.
struct Layout {
    out: String,
    indent: usize,
    step: usize,
}

impl Layout {
    /// `Format.text`. A newline INSIDE the text is a hard line break at the
    /// current `nest` indentation, as Lean's `Format.be` renders `text s`
    /// (`Init/Data/Format/Basic.lean`: `pushOutput` the prefix, then
    /// `pushNewline i.indent`, then the rest). Only a name component can carry
    /// one here (`Name.toString` escapes `«line⏎break»` but keeps the newline).
    /// Measured on the `ir_census/IrAdv` fixture: the pinned toolchain prints
    /// the callee `«line⏎break»` inside a body as `«line` / `  break» x_1;`;
    /// pushing the text verbatim lost that indentation.
    fn text(&mut self, s: &str) {
        let mut pieces = s.split('\n');
        if let Some(first) = pieces.next() {
            self.out.push_str(first);
        }
        for rest in pieces {
            self.line();
            self.out.push_str(rest);
        }
    }

    fn line(&mut self) {
        self.out.push('\n');
        self.out.extend(std::iter::repeat_n(' ', self.indent));
    }

    /// `Format.nest step (line ++ body)`.
    fn nested_body(&mut self, body: &FnBody) {
        self.indent += self.step;
        self.line();
        self.body(body);
        self.indent -= self.step;
    }

    /// `formatFnBody`'s `loop`.
    fn body(&mut self, b: &FnBody) {
        for instr in &b.instrs {
            match instr {
                Instr::VDecl { x, ty, e } => self.text(&format!(
                    "let x_{} : {} := {};",
                    x.0,
                    fmt_type(ty),
                    fmt_expr(e)
                )),
                Instr::JDecl { j, params, body } => {
                    self.text(&format!("block_{}{} :=", j.0, fmt_params(params)));
                    self.nested_body(body);
                    self.text(";");
                }
                Instr::Set { x, i, y } => {
                    self.text(&format!("set x_{}[{i}] := {};", x.0, fmt_arg(y)));
                }
                Instr::USet { x, i, y } => {
                    self.text(&format!("uset x_{}[{i}] := x_{};", x.0, y.0));
                }
                Instr::SSet {
                    x,
                    i,
                    offset,
                    y,
                    ty,
                } => self.text(&format!(
                    "sset x_{}[{i}, {offset}] : {} := x_{};",
                    x.0,
                    fmt_type(ty),
                    y.0
                )),
                Instr::SetTag { x, cidx } => {
                    self.text(&format!("setTag x_{} := {cidx};", x.0));
                }
                Instr::Inc { x, n, .. } => self.text(&format!("inc{} x_{};", rc_count(*n), x.0)),
                Instr::Dec { x, n, .. } => self.text(&format!("dec{} x_{};", rc_count(*n), x.0)),
                Instr::Del { x } => self.text(&format!("del x_{};", x.0)),
            }
            self.line();
        }
        match &b.terminal {
            Terminal::Case {
                x, x_type, alts, ..
            } => {
                self.text(&format!("case x_{} : {} of", x.0, fmt_type(x_type)));
                for alt in alts {
                    self.line();
                    match alt {
                        Alt::Ctor { info, body } => {
                            self.text(&format!("{} →", name_to_string(&info.name)));
                            self.nested_body(body);
                        }
                        Alt::Default { body } => {
                            self.text("default →");
                            self.nested_body(body);
                        }
                    }
                }
            }
            Terminal::Jmp { j, args } => self.text(&format!("jmp block_{}{}", j.0, fmt_args(args))),
            Terminal::Ret(x) => self.text(&format!("ret {}", fmt_arg(x))),
            Terminal::Unreachable => self.text("⊥"),
        }
    }
}

/// `inc`/`dec` print their count only when it is not 1 (`Format.sbracket`).
fn rc_count(n: u64) -> String {
    if n == 1 {
        String::new()
    } else {
        format!("[{n}]")
    }
}

/// `toString (d : Lean.IR.Decl)`: `formatDecl d 2` rendered by `Format.pretty`.
#[must_use]
pub(crate) fn format_decl(decl: &Decl) -> String {
    let mut layout = Layout {
        out: String::new(),
        indent: 0,
        step: 2,
    };
    match decl {
        Decl::FDecl {
            f,
            params,
            ty,
            body,
            ..
        } => {
            layout.text(&format!(
                "def {}{} : {} :=",
                name_to_string(f),
                fmt_params(params),
                fmt_type(ty)
            ));
            layout.nested_body(body);
        }
        Decl::Extern { f, params, ty, .. } => layout.text(&format!(
            "extern {}{} : {}",
            name_to_string(f),
            fmt_params(params),
            fmt_type(ty)
        )),
    }
    layout.out
}

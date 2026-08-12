// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Body emission for the Rust backend.
//!
//! Separated from the main emitter to keep file sizes under limits.

use super::{rust_byte_offset, scalar_setter_name, RustEmitter};
use crate::ir::{IRArg, IRType, JoinPointId, VarId};
use crate::ir_checker::IRError;
use crate::join_point_lower::{LoweredAlt, LoweredBody};

impl RustEmitter {
    /// Emit a lowered function body.
    pub(super) fn emit_body(&mut self, body: &LoweredBody) -> Result<(), IRError> {
        if self.emit_mutation(body)? {
            return Ok(());
        }
        match body {
            LoweredBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                self.record_var_type(*var, ty);
                let ty_str = self.emit_type(ty);
                let var_str = self.emit_var(*var);
                let value_str = self.emit_expr(value)?;
                self.writeln(&format!("let {}: {} = {};", var_str, ty_str, value_str));
                self.emit_body(rest)?;
            }
            LoweredBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                self.emit_case(*scrutinee, alts, default.as_deref())?;
            }
            LoweredBody::Ret(arg) => {
                self.writeln(&format!("return {};", self.emit_arg(arg)));
            }
            LoweredBody::Unreachable => {
                self.writeln("clean_panic(\"unreachable\");");
            }
            LoweredBody::JoinPoint {
                jp,
                params,
                init,
                body: jp_body,
            } => {
                self.emit_join_point(*jp, params, init, jp_body)?;
            }
            LoweredBody::JumpBreak { jp, assignments } => {
                self.emit_assignments(assignments);
                self.writeln(&format!("break {};", self.emit_jp_init_label(*jp)));
            }
            LoweredBody::JumpContinue { jp, assignments } => {
                self.emit_assignments(assignments);
                self.writeln(&format!("continue {};", self.emit_jp_label(*jp)));
            }
            _ => {
                return Err(IRError::UnexpectedBodyForm {
                    context: "Rust emit_body: non-mutation arm",
                });
            }
        }
        Ok(())
    }

    /// Emit mutation statements (Inc, Dec, Set, SetTag, USet, SSet).
    ///
    /// Returns true if body was handled, false if caller should dispatch.
    fn emit_mutation(&mut self, body: &LoweredBody) -> Result<bool, IRError> {
        match body {
            LoweredBody::Inc { var, n, rest } => {
                let v = self.emit_var(*var);
                if *n == 1 {
                    self.writeln(&format!("clean_inc({});", v));
                } else {
                    self.writeln(&format!("clean_inc_n({}, {});", v, n));
                }
                self.emit_body(rest)?;
            }
            LoweredBody::Dec { var, rest } => {
                self.writeln(&format!("clean_dec({});", self.emit_var(*var)));
                self.emit_body(rest)?;
            }
            LoweredBody::Set {
                var,
                idx,
                value,
                rest,
            } => {
                let v = self.emit_var(*var);
                let val = self.emit_var(*value);
                self.writeln(&format!("clean_ctor_set({}, {}, {});", v, idx, val));
                self.emit_body(rest)?;
            }
            LoweredBody::SetTag { var, tag, rest } => {
                self.writeln(&format!(
                    "clean_ctor_set_tag({}, {});",
                    self.emit_var(*var),
                    tag
                ));
                self.emit_body(rest)?;
            }
            LoweredBody::USet {
                var,
                idx,
                value,
                rest,
            } => {
                let v = self.emit_var(*var);
                let val = self.emit_var(*value);
                self.writeln(&format!("clean_ctor_set_usize({}, {}, {});", v, idx, val));
                self.emit_body(rest)?;
            }
            LoweredBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest,
            } => {
                let setter = scalar_setter_name(ty)?;
                self.writeln(&format!(
                    "{}({}, {}, {});",
                    setter,
                    self.emit_var(*var),
                    rust_byte_offset(*n, *offset),
                    self.emit_var(*value)
                ));
                self.emit_body(rest)?;
            }
            _ => return Ok(false),
        }
        Ok(true)
    }

    /// Emit case analysis as a `match` on constructor tag.
    fn emit_case(
        &mut self,
        scrutinee: VarId,
        alts: &[LoweredAlt],
        default: Option<&LoweredBody>,
    ) -> Result<(), IRError> {
        self.writeln(&format!(
            "match clean_obj_tag({}) {{",
            self.emit_var(scrutinee)
        ));
        self.indent();
        for alt in alts {
            self.writeln(&format!("{} => {{", alt.ctor.tag));
            self.indent();
            self.emit_body(&alt.body)?;
            self.dedent();
            self.writeln("}");
        }
        if let Some(def) = default {
            self.writeln("_ => {");
            self.indent();
            self.emit_body(def)?;
            self.dedent();
            self.writeln("}");
        } else {
            self.writeln("_ => {");
            self.indent();
            self.writeln("clean_panic(\"unreachable case\");");
            self.dedent();
            self.writeln("}");
        }
        self.dedent();
        self.writeln("}");
        Ok(())
    }

    /// Emit a join point as labeled block (init) + labeled loop (body).
    fn emit_join_point(
        &mut self,
        jp: JoinPointId,
        params: &[(VarId, IRType)],
        init: &LoweredBody,
        jp_body: &LoweredBody,
    ) -> Result<(), IRError> {
        for (var, ty) in params {
            self.record_var_type(*var, ty);
            let ty_str = self.emit_type(ty);
            let var_str = self.emit_var(*var);
            let default_str = self.emit_default(ty);
            self.writeln(&format!(
                "let mut {}: {} = {};",
                var_str, ty_str, default_str
            ));
        }
        let init_label = self.emit_jp_init_label(jp);
        self.writeln(&format!("{}: {{", init_label));
        self.indent();
        self.emit_body(init)?;
        self.dedent();
        self.writeln("}");
        let body_label = self.emit_jp_label(jp);
        self.writeln(&format!("{}: loop {{", body_label));
        self.indent();
        self.emit_body(jp_body)?;
        if !jp_body.is_terminating() {
            self.writeln(&format!("break {};", body_label));
        }
        self.dedent();
        self.writeln("}");
        Ok(())
    }

    /// Emit JP argument assignments.
    fn emit_assignments(&mut self, assignments: &[(VarId, IRArg)]) {
        for (var, arg) in assignments {
            self.writeln(&format!(
                "{} = {};",
                self.emit_var(*var),
                self.emit_arg(arg)
            ));
        }
    }
}

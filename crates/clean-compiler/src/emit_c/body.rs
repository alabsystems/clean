// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Body emission for the C backend.
//!
//! Separated from the main emitter to keep file sizes under limits.

use super::{c_byte_offset, c_scalar_setter_name, CEmitter};
use crate::ir::{IRAlt, IRBody};
use crate::ir_checker::IRError;

impl CEmitter {
    /// Emit an IR function body.
    pub fn emit_body(&mut self, body: &IRBody) -> Result<(), IRError> {
        if self.emit_mutation(body)? {
            return Ok(());
        }
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                self.record_var_type(*var, ty);
                let ty_str = self.emit_type(ty);
                let var_str = self.emit_var(*var);
                let value_str = self.emit_expr(value)?;
                self.writeln(&format!("{} {} = {};", ty_str, var_str, value_str));
                self.emit_body(rest)?;
            }

            IRBody::JDecl {
                jp,
                params,
                body: jp_body,
                rest,
            } => {
                // Store param VarIds for Jmp to look up. Part of #2040.
                self.jp_params
                    .insert(*jp, params.iter().map(|(v, _)| *v).collect());
                // Declare join point parameter variables before the goto target.
                // Jmp will assign to these variables before jumping.
                for (var, ty) in params {
                    self.record_var_type(*var, ty);
                    let ty_str = self.emit_type(ty);
                    let var_str = self.emit_var(*var);
                    self.writeln(&format!("{} {};", ty_str, var_str));
                }
                // Emit the rest (join point may be jumped to from rest)
                self.emit_body(rest)?;
                // Then emit join point body with label
                let label = self.emit_jp(*jp);
                self.writeln(&format!("{}:", label));
                self.indent();
                self.emit_body(jp_body)?;
                self.dedent();
            }

            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                self.emit_case(*scrutinee, alts, default.as_deref())?;
            }

            IRBody::Jmp { jp, args } => {
                self.emit_jmp(*jp, args);
            }

            IRBody::Ret(arg) => {
                let arg_str = self.emit_arg(arg);
                self.writeln(&format!("return {};", arg_str));
            }

            IRBody::Unreachable => {
                self.writeln("clean_panic(\"unreachable\");");
            }

            _ => {
                return Err(IRError::UnexpectedBodyForm {
                    context: "C emit_body: non-mutation arm",
                });
            }
        }
        Ok(())
    }

    /// Emit mutation statements (Inc, Dec, Set, SetTag, USet, SSet).
    ///
    /// Returns true if body was handled, false if caller should dispatch.
    fn emit_mutation(&mut self, body: &IRBody) -> Result<bool, IRError> {
        match body {
            IRBody::Inc { var, n, rest } => {
                let var_str = self.emit_var(*var);
                if *n == 1 {
                    self.writeln(&format!("clean_inc({});", var_str));
                } else {
                    self.writeln(&format!("clean_inc_n({}, {});", var_str, n));
                }
                self.emit_body(rest)?;
            }
            IRBody::Dec { var, rest } => {
                self.writeln(&format!("clean_dec({});", self.emit_var(*var)));
                self.emit_body(rest)?;
            }
            IRBody::Set {
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
            IRBody::SetTag { var, tag, rest } => {
                self.writeln(&format!(
                    "clean_ctor_set_tag({}, {});",
                    self.emit_var(*var),
                    tag
                ));
                self.emit_body(rest)?;
            }
            IRBody::USet {
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
            IRBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest,
            } => {
                let setter = c_scalar_setter_name(ty)?;
                self.writeln(&format!(
                    "{}({}, {}, {});",
                    setter,
                    self.emit_var(*var),
                    c_byte_offset(*n, *offset),
                    self.emit_var(*value)
                ));
                self.emit_body(rest)?;
            }
            _ => return Ok(false),
        }
        Ok(true)
    }

    /// Emit case analysis as a C `switch` on constructor tag.
    fn emit_case(
        &mut self,
        scrutinee: crate::ir::VarId,
        alts: &[IRAlt],
        default: Option<&IRBody>,
    ) -> Result<(), IRError> {
        let scrut_str = self.emit_var(scrutinee);
        // An unboxed scalar scrutinee (e.g. a `Bool` parameter lowered to
        // `uint8_t`) already *is* its own tag — `clean_obj_tag` expects a
        // `clean_obj*` and would be a type error on it. Switch on the value
        // directly in that case; only boxed objects go through `clean_obj_tag`.
        let switch_on = match self.var_types.get(&scrutinee) {
            Some(ty) if CEmitter::is_unboxed_scalar(ty) => scrut_str,
            _ => format!("clean_obj_tag({})", scrut_str),
        };
        self.writeln(&format!("switch ({}) {{", switch_on));
        self.indent();

        for alt in alts {
            self.writeln(&format!("case {}: {{", alt.ctor.tag));
            self.indent();
            self.emit_body(&alt.body)?;
            self.writeln("break;");
            self.dedent();
            self.writeln("}");
        }

        if let Some(def) = default {
            self.writeln("default: {");
            self.indent();
            self.emit_body(def)?;
            self.writeln("break;");
            self.dedent();
            self.writeln("}");
        }

        self.dedent();
        self.writeln("}");
        Ok(())
    }

    /// Emit a join point jump: assign args to parameter VarIds, then goto.
    fn emit_jmp(&mut self, jp: crate::ir::JoinPointId, args: &[crate::ir::IRArg]) {
        // Part of #2040: use actual VarId names (not _jpN_argI).
        if let Some(param_vars) = self.jp_params.get(&jp) {
            for (var, arg) in param_vars.clone().iter().zip(args.iter()) {
                let var_str = self.emit_var(*var);
                let arg_str = self.emit_arg(arg);
                self.writeln(&format!("{} = {};", var_str, arg_str));
            }
        } else {
            // Fallback: no JDecl seen (shouldn't happen in well-formed IR).
            for (i, arg) in args.iter().enumerate() {
                let arg_str = self.emit_arg(arg);
                self.writeln(&format!("_jp{}_arg{} = {};", jp.0, i, arg_str));
            }
        }
        self.writeln(&format!("goto {};", self.emit_jp(jp)));
    }
}

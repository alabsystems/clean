// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Construct profile of decoded IR: how often each IR constructor, flag and
//! type occurs across a census. It is the measured scope of the next
//! increment — an interpreter must implement every construct with a nonzero
//! count here — and it reads every field the text renderer does not
//! (`inc`/`dec` flags, `case` type ids, `box` types, `struct` names,
//! `CtorInfo.size`), so none of the decoded data is write-only.
//!
//! Printed by `clean olean ir-census --profile` as `PROFILE <key>=<count>`
//! lines on stderr; it is Clean-only output and is not part of the diffed
//! census text.

use std::collections::{BTreeMap, HashSet};

use super::module_ir::{InterpSource, MainSource, ModuleIr};
use super::types::{Alt, Decl, Expr, ExternEntry, FnBody, Instr, IrType, LitVal, Terminal};
use clean_kernel::Name;

/// Counts of IR constructs (see the module documentation).
#[derive(Debug, Default)]
pub(crate) struct IrProfile {
    counts: BTreeMap<&'static str, usize>,
    case_types: HashSet<Name>,
    named_struct_types: HashSet<Name>,
    max_jp: u64,
    max_var: u64,
}

impl IrProfile {
    fn add(&mut self, key: &'static str) {
        *self.counts.entry(key).or_default() += 1;
    }

    /// Fold another profile into this one.
    pub(crate) fn merge(&mut self, other: IrProfile) {
        for (key, n) in other.counts {
            *self.counts.entry(key).or_default() += n;
        }
        self.case_types.extend(other.case_types);
        self.named_struct_types.extend(other.named_struct_types);
        self.max_jp = self.max_jp.max(other.max_jp);
        self.max_var = self.max_var.max(other.max_var);
    }

    /// Profile one module: its sources and every declaration it carries.
    pub(crate) fn module(&mut self, ir: &ModuleIr) {
        self.add("modules");
        if ir.is_module {
            self.add("modules_module_system");
        }
        self.add(match ir.main_source {
            MainSource::Olean => "main_data_olean",
            MainSource::OleanPrivate => "main_data_olean_private",
        });
        for decl in &ir.olean_decls {
            self.decl(decl);
        }
        if ir.interp_source == InterpSource::IrFile {
            for decl in ir.ir_decls() {
                self.decl(decl);
            }
        }
    }

    fn decl(&mut self, decl: &Decl) {
        match decl {
            Decl::FDecl {
                params,
                ty,
                body,
                info,
                ..
            } => {
                self.add("decl_fdecl");
                if info.sorry_dep.is_some() {
                    self.add("decl_fdecl_sorry_dep");
                }
                if let Some(bounds) = &info.index_bounds {
                    self.add("decl_fdecl_index_bounds");
                    self.max_jp = self.max_jp.max(bounds.max_jp);
                    self.max_var = self.max_var.max(bounds.max_var);
                }
                for p in params {
                    if p.borrow {
                        self.add("param_borrowed");
                    }
                    self.ty(&p.ty);
                }
                self.ty(ty);
                self.body(body);
            }
            Decl::Extern {
                params, ty, ext, ..
            } => {
                self.add("decl_extern");
                for p in params {
                    self.ty(&p.ty);
                }
                self.ty(ty);
                for entry in &ext.entries {
                    self.add(match entry {
                        ExternEntry::Adhoc { .. } => "extern_entry_adhoc",
                        ExternEntry::Inline { .. } => "extern_entry_inline",
                        ExternEntry::Standard { .. } => "extern_entry_standard",
                        ExternEntry::Opaque => "extern_entry_opaque",
                    });
                }
            }
        }
    }

    fn ty(&mut self, ty: &IrType) {
        match ty {
            IrType::Struct {
                lean_type_name,
                types,
            } => {
                self.add("type_struct");
                if let Some(name) = lean_type_name {
                    self.named_struct_types.insert(name.clone());
                }
                types.iter().for_each(|t| self.ty(t));
            }
            IrType::Union {
                lean_type_name,
                types,
            } => {
                self.add("type_union");
                self.named_struct_types.insert(lean_type_name.clone());
                types.iter().for_each(|t| self.ty(t));
            }
            IrType::Float | IrType::Float32 => self.add("type_float"),
            IrType::Tagged => self.add("type_tagged"),
            IrType::Void => self.add("type_void"),
            _ => {}
        }
    }

    fn body(&mut self, body: &FnBody) {
        for instr in &body.instrs {
            match instr {
                Instr::VDecl { ty, e, .. } => {
                    self.ty(ty);
                    self.expr(e);
                }
                Instr::JDecl { params, body, .. } => {
                    self.add("instr_jdecl");
                    params.iter().for_each(|p| self.ty(&p.ty));
                    self.body(body);
                }
                Instr::Set { .. } => self.add("instr_set"),
                Instr::SetTag { .. } => self.add("instr_set_tag"),
                Instr::USet { .. } => self.add("instr_uset"),
                Instr::SSet { ty, .. } => {
                    self.add("instr_sset");
                    self.ty(ty);
                }
                Instr::Inc {
                    n,
                    check_ref,
                    persistent,
                    ..
                } => self.rc("instr_inc", *n, *check_ref, *persistent),
                Instr::Dec {
                    n,
                    check_ref,
                    persistent,
                    ..
                } => self.rc("instr_dec", *n, *check_ref, *persistent),
                Instr::Del { .. } => self.add("instr_del"),
            }
        }
        match &body.terminal {
            Terminal::Case {
                tid, x_type, alts, ..
            } => {
                self.add("term_case");
                self.case_types.insert(tid.clone());
                self.ty(x_type);
                for alt in alts {
                    match alt {
                        Alt::Ctor { body, .. } => self.body(body),
                        Alt::Default { body } => {
                            self.add("case_default_alt");
                            self.body(body);
                        }
                    }
                }
            }
            Terminal::Ret(_) => self.add("term_ret"),
            Terminal::Jmp { .. } => self.add("term_jmp"),
            Terminal::Unreachable => self.add("term_unreachable"),
        }
    }

    fn rc(&mut self, key: &'static str, n: u64, check_ref: bool, persistent: bool) {
        self.add(key);
        if n != 1 {
            self.add("rc_count_not_one");
        }
        if !check_ref {
            self.add("rc_known_object");
        }
        if persistent {
            self.add("rc_persistent");
        }
    }

    fn expr(&mut self, e: &Expr) {
        match e {
            Expr::Ctor { info, args } => {
                self.add("expr_ctor");
                if args.len() as u64 != info.size {
                    self.add("expr_ctor_args_differ_from_size");
                }
            }
            Expr::Reset { .. } => self.add("expr_reset"),
            Expr::Reuse { update_header, .. } => {
                self.add("expr_reuse");
                if *update_header {
                    self.add("expr_reuse_update_header");
                }
            }
            Expr::Proj { .. } => self.add("expr_proj"),
            Expr::UProj { .. } => self.add("expr_uproj"),
            Expr::SProj { .. } => self.add("expr_sproj"),
            Expr::Fap { .. } => self.add("expr_fap"),
            Expr::Pap { .. } => self.add("expr_pap"),
            Expr::Ap { .. } => self.add("expr_ap"),
            Expr::Box { ty, .. } => {
                self.add("expr_box");
                self.ty(ty);
            }
            Expr::Unbox { .. } => self.add("expr_unbox"),
            Expr::Lit(LitVal::Num(n)) => {
                self.add("expr_lit_num");
                if n.to_u64().is_none() {
                    self.add("expr_lit_num_over_u64");
                }
            }
            Expr::Lit(LitVal::Str(_)) => self.add("expr_lit_str"),
            Expr::IsShared { .. } => self.add("expr_is_shared"),
        }
    }

    /// The count recorded for `key` (0 when absent).
    #[cfg(test)]
    pub(crate) fn count(&self, key: &str) -> usize {
        self.counts.get(key).copied().unwrap_or(0)
    }

    /// `PROFILE` counts sorted by key, followed by summary statistics.
    pub(crate) fn render(&self) -> String {
        let mut out = String::new();
        for (key, n) in &self.counts {
            out.push_str(&format!("PROFILE {key}={n}\n"));
        }
        if self.counts.contains_key("decl_fdecl_index_bounds") {
            out.push_str(&format!("PROFILE max_jp={}\n", self.max_jp));
            out.push_str(&format!("PROFILE max_var={}\n", self.max_var));
        }
        out.push_str(&format!(
            "PROFILE distinct_case_types={}\n",
            self.case_types.len()
        ));
        out.push_str(&format!(
            "PROFILE distinct_struct_union_type_names={}\n",
            self.named_struct_types.len()
        ));
        out
    }
}

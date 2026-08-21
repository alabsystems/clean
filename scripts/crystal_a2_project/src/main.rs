// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! READER A of the crystal-A2 mint gate: crate-level trust-ir `.bin` -> the
//! canonical CORE MODULE text `clean-verify` commits and mints from.
//!
//! Reads the binary the compiler emitted, finds ONE function by name, applies
//! the PRODUCER's own canonical form (`trust_ir::format::canonicalize` — dense
//! SSA renumbering, the same rendering the committed `.trust-ir.txt` fixtures
//! are), projects it onto the fragment Clean's `IRModule` encodes, renumbers
//! the crate-level interning tables by first use, and prints the result.
//!
//! Fail-closed everywhere: an unmappable type, constant or instruction is an
//! error, never an approximation. Its output is a COMMITTED artifact
//! (`crates/clean-verify/src/spec/core_spec/generated/ir_*.core.txt`) that two
//! independent in-tree readers check, so a defect here shows up as a
//! disagreement in `tests/crystal_a2_mint.rs` rather than as a silent pass.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use sha2::{Digest, Sha256};
use trust_ir::constant::Constant;
use trust_ir::inst::Inst;
use trust_ir::ty::Ty;

mod ops;
use ops::{binop, cast, cc, fcmp, icmp, ovop, unop};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: a2project <crate.trust-ir.bin> <function-name> <out-dir> [slug]");
        std::process::exit(2);
    }
    let bin_path = &args[1];
    let fname = &args[2];
    let out_dir = &args[3];
    let slug = args
        .get(4)
        .cloned()
        .unwrap_or_else(|| fname.replace("::", "_"));

    let bytes = std::fs::read(bin_path).expect("read .bin");
    let mut h = Sha256::new();
    h.update(&bytes);
    let bin_sha = hex(&h.finalize());

    let raw = trust_ir::binary::deserialize_module(&bytes).expect("deserialize");
    // Trust's OWN published canonical form: dense SSA renumbering (block
    // params in block-id order, then instruction results in program order).
    // The emitted `.txt` this repo commits is exactly this rendering, so
    // reader A and reader B are normalized by the SAME rule -- and that rule
    // is the producer's, not one invented here. It also erases the builder's
    // arena layout, which `format.rs` states is not a logical property.
    let module = trust_ir::format::canonicalize(&raw);
    let (idx, func) = module
        .functions
        .iter()
        .enumerate()
        .find(|(_, f)| f.name == *fname)
        .unwrap_or_else(|| panic!("function {fname} not in {bin_path}"));
    let dup = module.functions.iter().filter(|f| f.name == *fname).count();
    assert_eq!(dup, 1, "function name is not unique in the artifact: {dup}");

    // Callee ids resolve to NAMES here and nowhere else: the artifact carries
    // the function table, the emitted TEXT does not. That is why the tag
    // table's `funcs` lane records the name reader A read and reader B cannot.
    let names: BTreeMap<u32, String> = module
        .functions
        .iter()
        .map(|f| (f.id.0, f.name.clone()))
        .collect();

    let mut p = Projector::default();
    let core = p
        .project(func)
        .unwrap_or_else(|e| panic!("projection refused: {e}"));
    let text = core;
    let digest = core_digest(&text);

    std::fs::create_dir_all(out_dir).expect("mkdir");
    std::fs::write(format!("{out_dir}/{slug}.core.txt"), &text).expect("write core");

    let mut prov = String::new();
    let _ = writeln!(prov, "{{");
    let _ = writeln!(
        prov,
        " \"reader\": \"A (trust-ir binary -> core), a2project\","
    );
    let _ = writeln!(prov, " \"dump\": {:?},", bin_path);
    let _ = writeln!(prov, " \"dump_sha256\": \"{bin_sha}\",");
    let _ = writeln!(prov, " \"module_name\": {:?},", module.name);
    let _ = writeln!(prov, " \"function_name\": {:?},", func.name);
    let _ = writeln!(prov, " \"artifact_func_index\": {idx},");
    let _ = writeln!(prov, " \"artifact_func_id\": {},", func.id.0);
    let _ = writeln!(prov, " \"artifact_functy_id\": {},", func.ty.0);
    // The three header facts reader B started COMPARING on 2026-08-20. Recorded
    // here so they stop being single-witness: until this runs, the linkage, the
    // calling convention and the producer token are pinned from reader B's
    // reading of the emitted TEXT alone, which is the mirror image of the
    // `switch-exhaustive-flag` slot standing on reader A alone.
    //
    // All three are printed by `trust_ir::display`'s `impl Display for
    // Function`, each suppressed when it holds its default — which is exactly
    // why `data/crystal_mint_blind_slots.json` was wrong to call them
    // unwitnessable, and exactly why they are spelled out unconditionally here.
    let _ = writeln!(prov, " \"artifact_linkage\": \"{}\",", func.linkage);
    let _ = writeln!(
        prov,
        " \"artifact_calling_conv\": \"{}\",",
        func.calling_conv
    );
    let producer = func
        .producer
        .as_ref()
        .map(ToString::to_string)
        .map(|value| json_string(&value))
        .unwrap_or_else(|| "null".to_owned());
    let _ = writeln!(prov, " \"artifact_producer\": {producer},");
    let _ = writeln!(prov, " \"core_digest\": \"{digest}\",");
    let _ = writeln!(prov, " \"crate_enum_ids_seen\": {:?},", p.enum_order);
    let _ = writeln!(prov, " \"crate_struct_ids_seen\": {:?},", p.struct_order);
    let _ = writeln!(prov, " \"crate_func_ids_seen\": {:?},", p.func_order);
    let seen_names: Vec<&str> = p
        .func_order
        .iter()
        .map(|id| {
            names
                .get(id)
                .map_or("<not in the artifact function table>", String::as_str)
        })
        .collect();
    let _ = writeln!(prov, " \"crate_func_names_seen\": {:?},", seen_names);
    let _ = writeln!(prov, " \"aligns_erased\": {:?},", p.aligns);
    let _ = writeln!(prov, " \"param_tys_erased\": {:?},", p.param_tys);
    let _ = writeln!(prov, " \"block_param_tys_erased\": {:?}", p.block_param_tys);
    let _ = writeln!(prov, "}}");
    std::fs::write(format!("{out_dir}/{slug}.core.prov.json"), prov).expect("write prov");

    println!(
        "{slug}\t{digest}\tfunc_index={idx}\tfunc_id={}\tenums={:?}",
        func.id.0, p.enum_order
    );
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Quote one UTF-8 string as JSON without adding a serialization dependency to
/// this sealed standalone projector. Rust's `Option<String>:?` is not JSON
/// (`Some("trust")` caused the current provenance bug), and `String`'s debug
/// escaping is not a promised JSON encoding either.
fn json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch <= '\u{1f}' => {
                use std::fmt::Write as _;
                let _ = write!(out, "\\u{:04x}", u32::from(ch));
            }
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn core_digest(text: &str) -> String {
    let mut h = Sha256::new();
    h.update(b"clean.ir_mint.core.v1\0");
    h.update(text.as_bytes());
    hex(&h.finalize())
}

#[cfg(test)]
mod tests {
    use super::json_string;

    #[test]
    fn producer_values_are_json_strings_not_rust_option_debug() {
        assert_eq!(json_string("trust"), r#""trust""#);
        assert_eq!(
            json_string("quoted \" producer\\line\n\u{0001}"),
            r#""quoted \" producer\\line\n\u0001""#
        );
    }
}

#[derive(Default)]
struct Projector {
    enums: BTreeMap<u32, u32>,
    structs: BTreeMap<u32, u32>,
    funcs: BTreeMap<u32, u32>,
    globals: BTreeMap<u32, u32>,
    enum_order: Vec<u32>,
    struct_order: Vec<u32>,
    func_order: Vec<u32>,
    aligns: Vec<String>,
    param_tys: Vec<String>,
    block_param_tys: Vec<String>,
}

pub(crate) type R<T> = Result<T, String>;

impl Projector {
    fn enum_id(&mut self, id: u32) -> u32 {
        let n = self.enums.len() as u32;
        *self.enums.entry(id).or_insert_with(|| {
            self.enum_order.push(id);
            n
        })
    }
    fn struct_id(&mut self, id: u32) -> u32 {
        let n = self.structs.len() as u32;
        *self.structs.entry(id).or_insert_with(|| {
            self.struct_order.push(id);
            n
        })
    }
    fn func_id(&mut self, id: u32) -> u32 {
        let n = self.funcs.len() as u32;
        *self.funcs.entry(id).or_insert_with(|| {
            self.func_order.push(id);
            n
        })
    }
    fn global_id(&mut self, id: u32) -> u32 {
        let n = self.globals.len() as u32;
        *self.globals.entry(id).or_insert(n)
    }

    fn project(&mut self, f: &trust_ir::Function) -> R<String> {
        let mut out = String::new();
        out.push_str("(module\n");
        out.push_str("  (funcs\n");
        // *** ONE NAMESPACE. *** The function's own id and its callee ids are
        // the same namespace by the specification's own semantics:
        // `ir_func_find` resolves a callee by scanning for a function whose OWN
        // id equals it, and `ir_call_exec` goes through `ir_func_find`. Until
        // 2026-08-20 this printed the literal `0` here while interning callees
        // from a counter that also started at 0, so in `level_is_zero` the
        // numeral 0 denoted BOTH the body and `<LevelArc as Deref>::deref` --
        // and swapping the two `@func.N` literals in the emitted text produced
        // a byte-identical core module for a different program. Interning the
        // own id FIRST gives it index 0, gives the self-call index 0 too, and
        // pushes every other callee above it.
        let self_idx = self.func_id(f.id.0);
        out.push_str(&format!("    (func {self_idx}\n"));
        // Parameters: the entry block's parameters ARE the function parameters
        // in this producer's shape; Clean's IRFunc carries their ids only.
        let entry = f
            .blocks
            .iter()
            .find(|b| b.id == f.entry)
            .ok_or_else(|| format!("entry block {:?} missing", f.entry))?;
        for p in &entry.params {
            self.param_tys.push(format!("{:?}", p.1));
        }
        let ps: Vec<String> = entry.params.iter().map(|p| p.0 .0.to_string()).collect();
        out.push_str(&format!("      (params{})\n", pad(&ps)));
        out.push_str(&format!("      (entry {})\n", f.entry.0));
        out.push_str("      (blocks\n");
        for b in &f.blocks {
            out.push_str(&format!("        (block {}\n", b.id.0));
            if b.id != f.entry {
                for p in &b.params {
                    self.block_param_tys.push(format!("bb{}:{:?}", b.id.0, p.1));
                }
            }
            let bps: Vec<String> = if b.id == f.entry {
                Vec::new()
            } else {
                b.params.iter().map(|p| p.0 .0.to_string()).collect()
            };
            out.push_str(&format!("          (params{})\n", pad(&bps)));
            out.push_str("          (nodes\n");
            for n in &b.body {
                let rs: Vec<String> = n.results.iter().map(|r| r.0.to_string()).collect();
                let i = self.inst(&n.inst)?;
                out.push_str(&format!("            (node (results{}) {})\n", pad(&rs), i));
            }
            out.push_str("          ))\n");
        }
        out.push_str("      ))\n");
        out.push_str("  )\n");
        out.push_str("  (globals)\n");
        out.push_str(")\n");
        Ok(out)
    }

    fn ty(&mut self, t: &Ty) -> R<String> {
        Ok(match t {
            Ty::Bool => "(bool)".into(),
            Ty::I8 => "(int 8)".into(),
            Ty::I16 => "(int 16)".into(),
            Ty::I32 => "(int 32)".into(),
            Ty::I64 => "(int 64)".into(),
            Ty::I128 => "(int 128)".into(),
            Ty::U8 => "(uint 8)".into(),
            Ty::U16 => "(uint 16)".into(),
            Ty::U32 => "(uint 32)".into(),
            Ty::U64 => "(uint 64)".into(),
            Ty::U128 => "(uint 128)".into(),
            Ty::F32 => "(float 32)".into(),
            Ty::F64 => "(float 64)".into(),
            Ty::Ptr => "(ptr)".into(),
            Ty::Unit => "(unit)".into(),
            Ty::Never => "(never)".into(),
            Ty::Struct(id) => format!("(struct {})", self.struct_id(id.0)),
            Ty::Enum(id) => format!("(enum {})", self.enum_id(id.0)),
            Ty::Ref(inner) => format!("(ref {})", self.ty(inner)?),
            Ty::RefMut(inner) => format!("(refmut {})", self.ty(inner)?),
            Ty::PtrConst(inner) => format!("(rawconst {})", self.ty(inner)?),
            Ty::PtrMut(inner) => format!("(rawmut {})", self.ty(inner)?),
            Ty::Rc(inner) => format!("(rc {})", self.ty(inner)?),
            other => return Err(format!("no Clean IRTy image for trust_ir::Ty::{other:?}")),
        })
    }

    fn cst(&mut self, c: &Constant) -> R<String> {
        Ok(match c {
            Constant::Int(v) => {
                if *v < 0 {
                    return Err(format!("negative Constant::Int({v}) has no Nat image"));
                }
                format!("(int {v})")
            }
            Constant::U128(v) => format!("(int {v})"),
            Constant::Bool(b) => format!("(bool {b})"),
            Constant::FnDef(id) => format!("(cfunc {})", self.func_id(id.0)),
            Constant::Float(x) => format!("(float {})", x.to_bits()),
            Constant::Aggregate(v) => {
                let mut s = String::from("(agg");
                for e in v {
                    s.push(' ');
                    s.push_str(&self.cst(e)?);
                }
                s.push(')');
                s
            }
            other => return Err(format!("no Clean IRConst image for {other:?}")),
        })
    }

    #[allow(clippy::too_many_lines)]
    fn inst(&mut self, i: &Inst) -> R<String> {
        Ok(match i {
            Inst::BinOp { op, ty, lhs, rhs } => format!(
                "(binop {} {} {} {})",
                binop(*op)?,
                self.ty(ty)?,
                lhs.0,
                rhs.0
            ),
            Inst::UnOp { op, ty, operand } => {
                format!("(unop {} {} {})", unop(*op)?, self.ty(ty)?, operand.0)
            }
            Inst::Overflow { op, ty, lhs, rhs } => format!(
                "(overflow {} {} {} {})",
                ovop(*op),
                self.ty(ty)?,
                lhs.0,
                rhs.0
            ),
            Inst::ICmp { op, ty, lhs, rhs } => {
                format!("(icmp {} {} {} {})", icmp(*op), self.ty(ty)?, lhs.0, rhs.0)
            }
            Inst::FCmp { op, ty, lhs, rhs } => {
                format!("(fcmp {} {} {} {})", fcmp(*op), self.ty(ty)?, lhs.0, rhs.0)
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => format!(
                "(cast {} {} {} {})",
                cast(*op)?,
                self.ty(src_ty)?,
                self.ty(dst_ty)?,
                operand.0
            ),
            Inst::Load {
                ty,
                ptr,
                volatile,
                align,
            } => {
                self.aligns.push(format!("load:{align:?}"));
                format!("(load {} {} {volatile})", self.ty(ty)?, ptr.0)
            }
            Inst::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            } => {
                self.aligns.push(format!("store:{align:?}"));
                format!("(store {} {} {} {volatile})", self.ty(ty)?, ptr.0, value.0)
            }
            Inst::Alloca { ty, count, align } => {
                self.aligns.push(format!("alloca:{align:?}"));
                let c = match count {
                    Some(v) => format!("(some {})", v.0),
                    None => "(none)".into(),
                };
                format!("(alloca {} {c})", self.ty(ty)?)
            }
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            } => {
                let ix: Vec<String> = indices.iter().map(|v| v.0.to_string()).collect();
                format!(
                    "(gep {} {} (idx{}) {inbounds})",
                    self.ty(pointee_ty)?,
                    base.0,
                    pad(&ix)
                )
            }
            Inst::PtrData { ptr_ty, ptr } => {
                format!("(ptrdata {} {})", self.ty(ptr_ty)?, ptr.0)
            }
            Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            } => format!(
                "(ptrmetadata {} {} {})",
                self.ty(ptr_ty)?,
                self.ty(metadata_ty)?,
                ptr.0
            ),
            Inst::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            } => format!(
                "(ptrfromparts {} {} {} {})",
                self.ty(ptr_ty)?,
                self.ty(metadata_ty)?,
                data.0,
                metadata.0
            ),
            Inst::Br { target, args } => {
                let a: Vec<String> = args.iter().map(|v| v.0.to_string()).collect();
                format!("(br {} (args{}))", target.0, pad(&a))
            }
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => {
                let ta: Vec<String> = then_args.iter().map(|v| v.0.to_string()).collect();
                let ea: Vec<String> = else_args.iter().map(|v| v.0.to_string()).collect();
                format!(
                    "(condbr {} {} (args{}) {} (args{}))",
                    cond.0,
                    then_target.0,
                    pad(&ta),
                    else_target.0,
                    pad(&ea)
                )
            }
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable,
            } => {
                let da: Vec<String> = default_args.iter().map(|v| v.0.to_string()).collect();
                let mut cs = String::from("(cases");
                for c in cases {
                    let ca: Vec<String> = c.args.iter().map(|v| v.0.to_string()).collect();
                    let _ = write!(cs, " (case {} {} (args{}))", c.value, c.target.0, pad(&ca));
                }
                cs.push(')');
                format!(
                    "(switch {} {} (args{}) {cs} {exhaustive_enum_unreachable})",
                    value.0,
                    default.0,
                    pad(&da)
                )
            }
            Inst::Call { callee, args } => {
                let a: Vec<String> = args.iter().map(|v| v.0.to_string()).collect();
                format!("(call {} (args{}))", self.func_id(callee.0), pad(&a))
            }
            Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            } => {
                let a: Vec<String> = args.iter().map(|v| v.0.to_string()).collect();
                format!(
                    "(callindirect {} {} (args{}) {})",
                    callee.0,
                    sig.0,
                    pad(&a),
                    cc(*calling_conv)
                )
            }
            Inst::Return { values } => {
                let v: Vec<String> = values.iter().map(|x| x.0.to_string()).collect();
                format!("(ret (vals{}))", pad(&v))
            }
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => format!("(extractfield {} {} {field})", self.ty(ty)?, aggregate.0),
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => format!(
                "(insertfield {} {} {field} {})",
                self.ty(ty)?,
                aggregate.0,
                value.0
            ),
            Inst::ExtractElement { ty, array, index } => {
                format!("(extractelement {} {} {})", self.ty(ty)?, array.0, index.0)
            }
            Inst::Const { ty, value } => {
                format!("(const {} {})", self.ty(ty)?, self.cst(value)?)
            }
            Inst::GlobalAddr { global } => {
                format!("(globaladdr {})", self.global_id(global.0))
            }
            Inst::Undef { ty } => format!("(undef {})", self.ty(ty)?),
            Inst::Assert { cond } => format!("(assert {})", cond.0),
            Inst::Unreachable => "(unreachable)".into(),
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => format!(
                "(select {} {} {} {})",
                self.ty(ty)?,
                cond.0,
                then_val.0,
                else_val.0
            ),
            other => {
                return Err(format!(
                    "no Clean IRInst image for trust_ir::Inst::{}",
                    variant_name(other)
                ))
            }
        })
    }
}

fn pad(v: &[String]) -> String {
    if v.is_empty() {
        String::new()
    } else {
        format!(" {}", v.join(" "))
    }
}

fn variant_name(i: &Inst) -> String {
    format!("{i:?}")
        .split(['{', '(', ' '])
        .next()
        .unwrap_or("?")
        .to_string()
}

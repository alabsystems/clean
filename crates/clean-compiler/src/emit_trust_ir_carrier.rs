// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The carrier back end: L5IR → trust-ir at the Rust ABI (Trust plan step
//! 3.2, C1–C3).
//!
//! The same core, the same pipeline, the same L5IR as [`super`]; a different
//! contract at the boundary. A Rust-callable Lean closure is compiled in a
//! CLOSED WORLD of carriers:
//!
//! * every value is a `bool`, a `u8`..`u64`, or (when `Nat` is carried) the
//!   pinned handle `handle<"Nat", "trust_bignum::Nat">` — never a `Ptr`, and
//!   never Clean's C-runtime object model;
//! * every call is to a function of the batch, to a declared Rust callee at
//!   its own symbol and carrier signature, or is one native carrier primitive
//!   ([`crate::carrier_prims`]) — never a bodyless `l_*` import;
//! * the only bodyless declarations are the Rust callees and the pinned `Nat`
//!   entry points the bodies actually call.
//!
//! Anything outside that world — a constructor, a projection out of an
//! object, a closure, a string, an unknown callee, an erased value in a value
//! position — is REFUSED by name ([`TrustIrError::Unsupported`]), never
//! lowered through the general back end's runtime calls. A refusal leaves
//! the declaration where it is today (Trust's planner or MIR lane).
//!
//! # `Nat` ownership (the handle has no reference count)
//!
//! L5IR counts references (`inc`/`dec`); a pinned handle is a uniquely owned
//! allocation with five entry points (`from_u64`, `add`, `sub`, `is_zero`,
//! `drop` — the five `trust-bignum` exports). The carrier back end therefore
//! ignores L5IR's reference counting on `Nat` and states its own discipline,
//! which needs nothing the IR does not show:
//!
//! 1. **Parameters are BORROWED**; a function never releases one.
//! 2. **A result is FRESH and OWNED by the caller.** `from_u64`, `add` and
//!    `sub` return fresh allocations (a property `trust-bignum` pins by
//!    test); a function that would return a borrowed handle returns a copy
//!    (`add(h, 0)`), so every handle a caller receives is its own.
//! 3. **Every handle a body allocates is released exactly once on each path,
//!    at the path's end**: a `ret` releases every owned handle in lexical
//!    scope except the one it returns; a jump to a join point releases every
//!    handle allocated since that join point's declaration except the ones it
//!    passes, and a passed handle that is not such a fresh one is copied, so
//!    a join point's handle parameters are always owned.
//! 4. A numeral at `Nat` is materialized at each use (`from_u64`), and is not
//!    materialized at all where it is a comparison against zero
//!    (`is_zero`).
//!
//! Nothing downstream checks lifetime (`TRUST.md` item 9(c) in trust-ir;
//! Trust's TCB row for the handle release); the discipline above is total
//! and local, so a reviewer can check it by reading this file.

use super::names::wire_name;
use super::TrustIrError;
use crate::carrier_prims::{
    carrier_prim, BoolOp, CarrierPrim, NatOp, ScalarBin, ScalarCmp, UIntWidth,
};
use crate::ir::{IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId};
use crate::rust_abi::RustExternSig;
use clean_kernel::Name;
use std::collections::{BTreeSet, HashMap};
use trust_ir::inst::{BinOp, CastOp, ICmpOp};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{BodyGate, CallingConv, Module};
use trust_ir_build::{FunctionBuilder, ModuleBuilder, TRUSTED_HANDLE_RUNTIMES};

/// The pinned `Nat` entry points this back end may call: exactly the five
/// `trust-bignum` exports. Every other pinned role validates and fails to
/// link, so it is never declared.
pub(crate) const NAT_ROLES: [&str; 5] = ["from_u64", "add", "sub", "is_zero", "drop"];

/// The handle row's `(name, runtime)` pair.
const NAT_HANDLE: (&str, &str) = ("Nat", "trust_bignum::Nat");

/// What the carrier back end emitted.
pub(crate) struct CarrierModule {
    /// The module (not yet finalized: the caller pins the target and gates).
    pub(crate) module: Module,
    /// Each emitted batch function's Clean name and id.
    pub(crate) functions: Vec<(Name, FuncId)>,
    /// Whether any `Nat` handle occurs.
    pub(crate) handle_bearing: bool,
}

/// A callee of the batch: a batch function or a Rust callee.
#[derive(Clone)]
struct Callee {
    id: FuncId,
    params: Vec<Ty>,
    returns: Vec<Ty>,
}

/// Emit `decls` at the carrier ABI. Two emissions: the first declares all
/// [`NAT_ROLES`] and records which the bodies call; the second declares
/// exactly those, so the module states only the entry points it calls.
pub(crate) fn emit_carrier_module(
    decls: &[IRDecl],
    rust_externs: &[RustExternSig],
    nat_handles: bool,
    module_name: &str,
) -> Result<CarrierModule, TrustIrError> {
    let all: BTreeSet<&'static str> = if nat_handles {
        NAT_ROLES.into_iter().collect()
    } else {
        BTreeSet::new()
    };
    let (_, used) = emit_with_roles(decls, rust_externs, nat_handles, module_name, &all)?;
    let (out, again) = emit_with_roles(decls, rust_externs, nat_handles, module_name, &used)?;
    debug_assert_eq!(used, again, "the role set is a fixed point of emission");
    Ok(out)
}

fn unsupported(decl: &Name, what: impl std::fmt::Display) -> TrustIrError {
    TrustIrError::Unsupported(format!(
        "Rust ABI: `{decl}` {what}, which is outside the carrier closure (bool, u8..u64, Nat at \
         the pinned handle; calls to the batch, to declared Rust callees and to native carrier \
         primitives). Options: keep this declaration on the planner or MIR lane, or spell it \
         inside the carrier closure."
    ))
}

/// The carrier lowering of an L5IR type in a signature or binding.
fn carrier_ty(ty: &IRType, nat_handles: bool) -> Option<Ty> {
    Some(match ty {
        IRType::Bool => Ty::Bool,
        IRType::UInt8 => Ty::U8,
        IRType::UInt16 => Ty::U16,
        IRType::UInt32 => Ty::U32,
        // `USize` appears only as the staging type of a `Nat` numeral.
        IRType::UInt64 | IRType::USize => Ty::U64,
        IRType::Object | IRType::TObject if nat_handles => Ty::handle(NAT_HANDLE.0, NAT_HANDLE.1),
        _ => return None,
    })
}

fn emit_with_roles(
    decls: &[IRDecl],
    rust_externs: &[RustExternSig],
    nat_handles: bool,
    module_name: &str,
    roles: &BTreeSet<&'static str>,
) -> Result<(CarrierModule, BTreeSet<&'static str>), TrustIrError> {
    let mut mb = ModuleBuilder::new(module_name.to_string());
    mb.set_default_producer(trust_ir::Producer::Clean);

    // One `FuncTyId` per distinct signature this back end adds.
    let mut func_tys: Vec<((Vec<Ty>, Vec<Ty>), trust_ir::value::FuncTyId)> = Vec::new();
    let mut intern = |mb: &mut ModuleBuilder, params: &[Ty], returns: &[Ty]| {
        if let Some((_, id)) = func_tys
            .iter()
            .find(|((p, r), _)| p.as_slice() == params && r.as_slice() == returns)
        {
            return *id;
        }
        let id = mb.add_func_type(params.to_vec(), returns.to_vec());
        func_tys.push(((params.to_vec(), returns.to_vec()), id));
        id
    };

    let mut callees: HashMap<Name, Callee> = HashMap::new();
    // 1. The Rust callees, at their own symbols and carrier signatures.
    for ext in rust_externs {
        let params = ext
            .params
            .iter()
            .map(|t| {
                carrier_ty(t, false)
                    .ok_or_else(|| unsupported(&ext.name, "has a non-carrier parameter"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let returns = vec![carrier_ty(&ext.ret, false)
            .ok_or_else(|| unsupported(&ext.name, "has a non-carrier result"))?];
        let ty = intern(&mut mb, &params, &returns);
        let mut fb = mb.function(ext.symbol.clone(), ty);
        // The Rust function's own convention: a same-compiler Rust call, not
        // a foreign-ABI boundary.
        fb.set_calling_conv(CallingConv::Rust);
        if ext.symbol != ext.name.to_string() {
            fb.set_display_path(ext.name.to_string());
        }
        let id = fb.build();
        callees.insert(
            ext.name.clone(),
            Callee {
                id,
                params,
                returns,
            },
        );
    }
    // 2. The pinned `Nat` entry points the bodies call.
    let nat = if roles.is_empty() {
        None
    } else {
        let pin = TRUSTED_HANDLE_RUNTIMES
            .iter()
            .find(|p| p.name == NAT_HANDLE.0 && p.runtime == NAT_HANDLE.1)
            .ok_or_else(|| {
                TrustIrError::Unsupported("the pinned Nat handle row is absent".into())
            })?;
        let wanted: Vec<&str> = NAT_ROLES
            .into_iter()
            .filter(|r| roles.contains(r))
            .collect();
        let declared = mb
            .declare_handle_runtime_roles(pin, &wanted)
            .map_err(|e| TrustIrError::Unsupported(format!("pinned Nat entry points: {e:?}")))?;
        let mut ids = HashMap::new();
        for role in wanted {
            let id = declared.entry(role).ok_or_else(|| {
                TrustIrError::Unsupported(format!("pinned Nat role `{role}` absent"))
            })?;
            ids.insert(role, id);
        }
        Some(ids)
    };
    let base = rust_externs.len() as u32 + nat.as_ref().map_or(0, |m| m.len() as u32);

    // 3. The batch functions: ids by declaration order, signatures up front.
    let mut sigs = Vec::with_capacity(decls.len());
    for (idx, decl) in decls.iter().enumerate() {
        if callees.contains_key(&decl.name) {
            return Err(unsupported(
                &decl.name,
                "is both a batch function and a Rust callee",
            ));
        }
        let params = decl
            .params
            .iter()
            .map(|(_, t)| {
                carrier_ty(t, nat_handles).ok_or_else(|| {
                    unsupported(&decl.name, format_args!("has a parameter at `{t:?}`"))
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let returns = vec![carrier_ty(&decl.return_type, nat_handles).ok_or_else(|| {
            unsupported(&decl.name, format_args!("returns `{:?}`", decl.return_type))
        })?];
        let ty = intern(&mut mb, &params, &returns);
        sigs.push(ty);
        callees.insert(
            decl.name.clone(),
            Callee {
                id: FuncId::new(base + idx as u32),
                params,
                returns,
            },
        );
    }

    let mut used = BTreeSet::new();
    let mut functions = Vec::with_capacity(decls.len());
    for (decl, ty) in decls.iter().zip(sigs) {
        let symbol = wire_name(&decl.name);
        let human = decl.name.to_string();
        let mut fb = mb.function(symbol.clone(), ty);
        // A Rust caller calls a Lean `def` as a Rust `fn`: the Rust
        // convention, which is also what Trust's join requires of the
        // definition a Rust declaration is linked to.
        fb.set_calling_conv(CallingConv::Rust);
        // No claim: the authority to ship this body is Trust's carrier gate.
        fb.set_body_gate(BodyGate::Ungated);
        if symbol != human {
            fb.set_display_path(human);
        }
        let entry = fb.create_block();
        let callee = callees
            .get(&decl.name)
            .cloned()
            .ok_or_else(|| unsupported(&decl.name, "has no recorded signature"))?;
        let mut cx = CarrierFn {
            fb: &mut fb,
            decl: &decl.name,
            callees: &callees,
            nat: nat.as_ref(),
            nat_handles,
            used: &mut used,
            vars: HashMap::new(),
            owned: Vec::new(),
            jps: HashMap::new(),
            returns: callee.returns.clone(),
            literals: HashMap::new(),
        };
        for ((var, _), pty) in decl.params.iter().zip(&callee.params) {
            let v = cx.fb.add_block_param(entry, pty.clone());
            cx.vars.insert(*var, Bound::Value(v, pty.clone()));
        }
        cx.fb.set_entry(entry);
        cx.fb.switch_to_block(entry);
        cx.body(&decl.body)?;
        let id = fb.build();
        functions.push((decl.name.clone(), id));
    }
    let module = mb.build()?;
    let mut symbols = BTreeSet::new();
    if let Some(dup) = module
        .functions
        .iter()
        .find(|f| !symbols.insert(f.name.as_str()))
    {
        return Err(TrustIrError::Unsupported(format!(
            "Rust ABI: two functions of the module share the symbol `{}`. Options: give the \
             Rust callee its own mangled symbol.",
            dup.name
        )));
    }
    let handle_bearing = module.func_types.iter().any(|ft| {
        ft.params
            .iter()
            .chain(&ft.returns)
            .any(|t| matches!(t, Ty::Handle(_)))
    });
    Ok((
        CarrierModule {
            module,
            functions,
            handle_bearing,
        },
        used,
    ))
}

/// What an L5IR variable is bound to.
#[derive(Clone)]
enum Bound {
    /// An SSA value of the given type.
    Value(ValueId, Ty),
    /// A `Nat` that is a boxed scalar not yet materialized as a handle: the
    /// scalar, its width type, and its value when it is a literal.
    NatOfScalar(ValueId, Ty, Option<u64>),
    /// An erased value: usable only where it is dropped.
    Erased,
}

struct JoinPoint {
    block: BlockId,
    /// `owned.len()` at the join point's declaration.
    mark: usize,
    params: Vec<Ty>,
}

struct CarrierFn<'a, 'b> {
    fb: &'a mut FunctionBuilder<'b>,
    decl: &'a Name,
    callees: &'a HashMap<Name, Callee>,
    nat: Option<&'a HashMap<&'static str, FuncId>>,
    nat_handles: bool,
    used: &'a mut BTreeSet<&'static str>,
    vars: HashMap<VarId, Bound>,
    /// The handles this body owns, in allocation order, lexically scoped.
    owned: Vec<ValueId>,
    jps: HashMap<JoinPointId, JoinPoint>,
    returns: Vec<Ty>,
    /// The value of every integer constant this body materialized.
    literals: HashMap<ValueId, u64>,
}

fn is_handle(ty: &Ty) -> bool {
    matches!(ty, Ty::Handle(_))
}

fn handle_ty() -> Ty {
    Ty::handle(NAT_HANDLE.0, NAT_HANDLE.1)
}

impl CarrierFn<'_, '_> {
    fn refuse(&self, what: impl std::fmt::Display) -> TrustIrError {
        unsupported(self.decl, what)
    }

    fn role(&mut self, role: &'static str) -> Result<FuncId, TrustIrError> {
        self.used.insert(role);
        self.nat
            .and_then(|m| m.get(role).copied())
            .ok_or_else(|| self.refuse(format_args!("needs the pinned Nat entry point `{role}`")))
    }

    fn nat_call(
        &mut self,
        role: &'static str,
        args: Vec<ValueId>,
    ) -> Result<ValueId, TrustIrError> {
        let id = self.role(role)?;
        Ok(self.fb.call(id, args))
    }

    fn release(&mut self, h: ValueId) -> Result<(), TrustIrError> {
        let id = self.role("drop")?;
        self.fb.call_void(id, vec![h]);
        Ok(())
    }

    /// A fresh owned handle holding the value `v` of scalar type `ty`.
    fn handle_of_scalar(&mut self, v: ValueId, ty: &Ty) -> Result<ValueId, TrustIrError> {
        let wide = match ty {
            Ty::U64 => v,
            Ty::U8 | Ty::U16 | Ty::U32 => self.fb.cast(CastOp::ZExt, ty.clone(), Ty::U64, v),
            other => return Err(self.refuse(format_args!("boxes a `{other:?}` as a Nat"))),
        };
        let h = self.nat_call("from_u64", vec![wide])?;
        self.owned.push(h);
        Ok(h)
    }

    /// A fresh owned copy of the handle `h` (`add(h, 0)`).
    fn copy(&mut self, h: ValueId) -> Result<ValueId, TrustIrError> {
        let zero = self.fb.iconst(Ty::U64, 0);
        let z = self.nat_call("from_u64", vec![zero])?;
        let c = self.nat_call("add", vec![h, z])?;
        self.release(z)?;
        self.owned.push(c);
        Ok(c)
    }

    fn bound(&self, arg: &IRArg) -> Result<Bound, TrustIrError> {
        match arg {
            IRArg::Erased => Ok(Bound::Erased),
            IRArg::Var(v) => self
                .vars
                .get(v)
                .cloned()
                .ok_or(TrustIrError::UndefinedVariable(*v)),
        }
    }

    /// A scalar operand of type `want`.
    fn scalar(&self, arg: &IRArg, want: &Ty) -> Result<ValueId, TrustIrError> {
        match self.bound(arg)? {
            Bound::Value(v, ty) if ty == *want => Ok(v),
            Bound::Value(_, ty) => {
                Err(self.refuse(format_args!("passes `{ty:?}` where `{want:?}` is expected")))
            }
            Bound::NatOfScalar(..) => Err(self.refuse("uses a Nat where a scalar is expected")),
            Bound::Erased => Err(self.refuse("uses an erased value")),
        }
    }

    /// A handle operand: `(handle, is_temporary)`. A not-yet-materialized
    /// `Nat` is materialized here, for this use only.
    fn handle(&mut self, arg: &IRArg) -> Result<(ValueId, bool), TrustIrError> {
        match self.bound(arg)? {
            Bound::Value(v, ty) if is_handle(&ty) => Ok((v, false)),
            Bound::NatOfScalar(v, ty, _) => {
                let h = self.handle_of_scalar(v, &ty)?;
                // A temporary: not part of the lexical owned set.
                self.owned.pop();
                Ok((h, true))
            }
            Bound::Value(_, ty) => Err(self.refuse(format_args!("uses `{ty:?}` as a Nat"))),
            Bound::Erased => Err(self.refuse("uses an erased value as a Nat")),
        }
    }

    fn literal_of(&self, arg: &IRArg) -> Option<u64> {
        match self.bound(arg).ok()? {
            Bound::NatOfScalar(_, _, lit) => lit,
            _ => None,
        }
    }

    fn drop_temps(&mut self, temps: &[(ValueId, bool)]) -> Result<(), TrustIrError> {
        for (h, temp) in temps {
            if *temp {
                self.release(*h)?;
            }
        }
        Ok(())
    }

    fn body(&mut self, body: &IRBody) -> Result<(), TrustIrError> {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                let bound = if matches!(ty, IRType::Erased | IRType::Void) {
                    Bound::Erased
                } else {
                    self.expr(value, ty)?
                };
                self.vars.insert(*var, bound);
                self.body(rest)
            }
            // Reference counting is the object model's; the carrier closure
            // states its own discipline (module docs) and has no other object.
            IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => self.body(rest),
            IRBody::Set { .. }
            | IRBody::SetTag { .. }
            | IRBody::USet { .. }
            | IRBody::SSet { .. } => Err(self.refuse("mutates an object in place")),
            IRBody::JDecl {
                jp,
                params,
                body,
                rest,
            } => {
                let block = self.fb.create_block();
                let mark = self.owned.len();
                let mut ptys = Vec::with_capacity(params.len());
                for (pvar, pty) in params {
                    let ty = carrier_ty(pty, self.nat_handles).ok_or_else(|| {
                        self.refuse(format_args!("has a join point parameter at `{pty:?}`"))
                    })?;
                    let v = self.fb.add_block_param(block, ty.clone());
                    if is_handle(&ty) {
                        self.owned.push(v);
                    }
                    self.vars.insert(*pvar, Bound::Value(v, ty.clone()));
                    ptys.push(ty);
                }
                self.jps.insert(
                    *jp,
                    JoinPoint {
                        block,
                        mark,
                        params: ptys,
                    },
                );
                let cont = self.fb.create_block();
                self.fb.br(cont, vec![]);
                self.fb.switch_to_block(block);
                self.body(body)?;
                self.owned.truncate(mark);
                self.fb.switch_to_block(cont);
                self.body(rest)
            }
            IRBody::Jmp { jp, args } => self.jump(*jp, args),
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => self.case(*scrutinee, alts, default.as_deref()),
            IRBody::Ret(arg) => self.ret(arg),
            IRBody::Unreachable => {
                self.fb.unreachable();
                Ok(())
            }
        }
    }

    fn ret(&mut self, arg: &IRArg) -> Result<(), TrustIrError> {
        let returns = self.returns.clone();
        let [ret_ty] = returns.as_slice() else {
            return Err(self.refuse("has a multi-value return"));
        };
        let value = if is_handle(ret_ty) {
            let (h, temp) = self.handle(arg)?;
            if temp || self.owned.contains(&h) {
                h
            } else {
                // A borrowed parameter: the caller receives its own copy.
                let c = self.copy(h)?;
                self.owned.pop();
                c
            }
        } else {
            self.scalar(arg, ret_ty)?
        };
        let owned = self.owned.clone();
        for h in owned {
            if h != value {
                self.release(h)?;
            }
        }
        self.fb.ret(vec![value]);
        Ok(())
    }

    fn jump(&mut self, jp: JoinPointId, args: &[IRArg]) -> Result<(), TrustIrError> {
        let (block, mark, params) = {
            let info = self
                .jps
                .get(&jp)
                .ok_or(TrustIrError::UndefinedJoinPoint(jp))?;
            (info.block, info.mark, info.params.clone())
        };
        let live: Vec<IRArg> = args
            .iter()
            .filter(|a| matches!(a, IRArg::Var(_)))
            .cloned()
            .collect();
        if live.len() != params.len() {
            return Err(self.refuse("jumps with an erased join point argument"));
        }
        let fresh: Vec<ValueId> = self.owned[mark.min(self.owned.len())..].to_vec();
        let mut transferred: Vec<ValueId> = Vec::new();
        let mut vals = Vec::with_capacity(live.len());
        for (arg, pty) in live.iter().zip(&params) {
            if is_handle(pty) {
                let (h, temp) = self.handle(arg)?;
                let v = if temp {
                    h
                } else if fresh.contains(&h) && !transferred.contains(&h) {
                    transferred.push(h);
                    h
                } else {
                    let c = self.copy(h)?;
                    self.owned.pop();
                    c
                };
                vals.push(v);
            } else {
                vals.push(self.scalar(arg, pty)?);
            }
        }
        for h in fresh {
            if !transferred.contains(&h) {
                self.release(h)?;
            }
        }
        self.fb.br(block, vals);
        Ok(())
    }

    fn case(
        &mut self,
        scrutinee: VarId,
        alts: &[IRAlt],
        default: Option<&IRBody>,
    ) -> Result<(), TrustIrError> {
        let (scrut, ty) = match self.vars.get(&scrutinee) {
            Some(Bound::Value(v, ty)) if !is_handle(ty) => (*v, ty.clone()),
            _ => return Err(self.refuse("matches on an object")),
        };
        let mark = self.owned.len();
        if ty == Ty::Bool {
            let mut sides: [Option<&IRBody>; 2] = [None, None];
            for alt in alts {
                let slot = sides
                    .get_mut(alt.ctor.tag as usize)
                    .ok_or_else(|| self.refuse("matches a Bool on a non-Bool tag"))?;
                if slot.replace(&alt.body).is_some() {
                    return Err(self.refuse("matches a Bool tag twice"));
                }
            }
            let then_blk = self.fb.create_block();
            let else_blk = self.fb.create_block();
            self.fb.condbr(scrut, then_blk, vec![], else_blk, vec![]);
            for (blk, side) in [(then_blk, sides[1]), (else_blk, sides[0])] {
                self.fb.switch_to_block(blk);
                match side.or(default) {
                    Some(b) => self.body(b)?,
                    None => self.fb.unreachable(),
                }
                self.owned.truncate(mark);
            }
            return Ok(());
        }
        use trust_ir::constant::Constant;
        use trust_ir::inst::SwitchCase;
        let mut cases = Vec::with_capacity(alts.len());
        let mut blocks = Vec::with_capacity(alts.len());
        for alt in alts {
            let blk = self.fb.create_block();
            cases.push(SwitchCase {
                value: Constant::Int(i128::from(alt.ctor.tag)),
                target: blk,
                args: vec![],
            });
            blocks.push(blk);
        }
        let default_blk = self.fb.create_block();
        self.fb.switch(scrut, cases, default_blk, vec![]);
        for (alt, blk) in alts.iter().zip(blocks) {
            self.fb.switch_to_block(blk);
            self.body(&alt.body)?;
            self.owned.truncate(mark);
        }
        self.fb.switch_to_block(default_blk);
        match default {
            Some(d) => self.body(d)?,
            None => self.fb.unreachable(),
        }
        self.owned.truncate(mark);
        Ok(())
    }

    fn expr(&mut self, expr: &IRExpr, ty: &IRType) -> Result<Bound, TrustIrError> {
        match expr {
            // A nullary `Bool` constructor reaches here as its tag.
            IRExpr::Lit(IRLiteral::UInt8(t)) if *ty == IRType::Bool && *t <= 1 => {
                Ok(Bound::Value(self.fb.bool_const(*t == 1), Ty::Bool))
            }
            IRExpr::Lit(IRLiteral::UInt32(t)) if *ty == IRType::Bool && *t <= 1 => {
                Ok(Bound::Value(self.fb.bool_const(*t == 1), Ty::Bool))
            }
            IRExpr::Lit(lit) => self.literal(lit),
            // A boxed `Bool` is dispatched on by tag (`false` = 0, `true` =
            // 1), which is the `Bool` itself: the box exists only because a
            // `case` with a default arm asks for an object scrutinee. Any
            // other use of it is a `Bool` where a `Nat` is expected, and is
            // refused there.
            IRExpr::Box {
                ty: IRType::Bool,
                arg,
            } => match self.bound(arg)? {
                Bound::Value(v, Ty::Bool) => Ok(Bound::Value(v, Ty::Bool)),
                _ => Err(self.refuse("boxes a value that is not its Bool")),
            },
            IRExpr::Box { ty: from, arg } => {
                if !self.nat_handles {
                    return Err(self.refuse("boxes a scalar"));
                }
                let width = carrier_ty(from, false)
                    .filter(|t| *t != Ty::Bool)
                    .ok_or_else(|| self.refuse(format_args!("boxes a `{from:?}`")))?;
                let v = match self.bound(arg)? {
                    Bound::Value(v, t) if t == width => v,
                    _ => return Err(self.refuse("boxes a value that is not its scalar")),
                };
                let lit = self.literals.get(&v).copied();
                Ok(Bound::NatOfScalar(v, width, lit))
            }
            IRExpr::Apply { fn_id, args } => self.apply(&fn_id.0, args),
            // `Bool.true`/`Bool.false` as an object constructor: the `Bool`.
            IRExpr::Ctor { info, args }
                if args.is_empty()
                    && matches!(info.name.to_string().as_str(), "Bool.false" | "Bool.true") =>
            {
                let b = info.name.to_string() == "Bool.true";
                Ok(Bound::Value(self.fb.bool_const(b), Ty::Bool))
            }
            // An unbox of a value the closure already holds unboxed (the box
            // above, or a `Bool` constructor) is that value.
            IRExpr::Unbox { ty: to, arg } => match (self.bound(arg)?, carrier_ty(to, false)) {
                (Bound::Value(v, t), Some(want)) if t == want => Ok(Bound::Value(v, t)),
                _ => Err(self.refuse(format_args!("unboxes an object to `{to:?}`"))),
            },
            // A projection out of an unboxed scalar carrier is that carrier
            // (`Char.val`, `UInt8.toBitVec` at the same width).
            IRExpr::Proj {
                arg: IRArg::Var(v),
                ty: pty,
                ..
            }
            | IRExpr::SProj {
                var: v, ty: pty, ..
            } if matches!(self.vars.get(v), Some(Bound::Value(_, t)) if Some(t.clone()) == carrier_ty(pty, false)) => {
                Ok(self.vars.get(v).cloned().unwrap_or(Bound::Erased))
            }
            other => Err(self.refuse(format_args!("contains `{}`", expr_kind(other)))),
        }
    }

    fn apply(&mut self, name: &Name, args: &[IRArg]) -> Result<Bound, TrustIrError> {
        if let Some(callee) = self.callees.get(name).cloned() {
            if args.len() != callee.params.len() {
                return Err(self.refuse(format_args!(
                    "calls `{name}` with {} arguments for {} parameters",
                    args.len(),
                    callee.params.len()
                )));
            }
            let mut vals = Vec::with_capacity(args.len());
            let mut temps = Vec::new();
            for (arg, pty) in args.iter().zip(&callee.params) {
                if is_handle(pty) {
                    let (h, temp) = self.handle(arg)?;
                    vals.push(h);
                    temps.push((h, temp));
                } else {
                    vals.push(self.scalar(arg, pty)?);
                }
            }
            let [ret] = callee.returns.as_slice() else {
                return Err(self.refuse(format_args!("calls `{name}`, which has no single result")));
            };
            let r = self.fb.call(callee.id, vals);
            // Callees borrow their arguments (module docs, rule 1).
            self.drop_temps(&temps)?;
            if is_handle(ret) {
                self.owned.push(r);
            }
            return Ok(Bound::Value(r, ret.clone()));
        }
        let prim = carrier_prim(name, self.nat_handles).ok_or_else(|| {
            self.refuse(format_args!(
                "calls `{name}`, which is neither in the batch, a declared Rust callee, nor a \
                 native carrier primitive"
            ))
        })?;
        self.prim(prim, args)
    }

    fn prim(&mut self, prim: CarrierPrim, args: &[IRArg]) -> Result<Bound, TrustIrError> {
        let arity = prim.params().len();
        if args.len() != arity {
            return Err(self.refuse(format_args!(
                "applies a primitive of arity {arity} to {} arguments",
                args.len()
            )));
        }
        match prim {
            CarrierPrim::Bin(op, w) => {
                let t = carrier_ty(&w.ir_type(), false)
                    .ok_or_else(|| self.refuse("has a primitive at a non-carrier width"))?;
                let a = self.scalar(&args[0], &t)?;
                let b = self.scalar(&args[1], &t)?;
                // Lean shifts are total: their UInt amount is reduced modulo
                // the word width. The independent IR reader proves the URem
                // divisor nonzero and its result below that width. A raw
                // machine shift would be undefined for some valid Lean inputs.
                let b = if matches!(op, ScalarBin::Shl | ScalarBin::LShr) {
                    let width = match w {
                        UIntWidth::W8 => 8,
                        UIntWidth::W16 => 16,
                        UIntWidth::W32 => 32,
                        UIntWidth::W64 => 64,
                    };
                    let modulus = self.fb.iconst(t.clone(), width);
                    self.fb.binop(BinOp::URem, t.clone(), b, modulus)
                } else {
                    b
                };
                let op = match op {
                    ScalarBin::Add => BinOp::Add,
                    ScalarBin::Sub => BinOp::Sub,
                    ScalarBin::Mul => BinOp::Mul,
                    ScalarBin::And => BinOp::And,
                    ScalarBin::Or => BinOp::Or,
                    ScalarBin::Xor => BinOp::Xor,
                    ScalarBin::Shl => BinOp::Shl,
                    ScalarBin::LShr => BinOp::LShr,
                };
                Ok(Bound::Value(self.fb.binop(op, t.clone(), a, b), t))
            }
            CarrierPrim::Cmp(op, w) => {
                let t = carrier_ty(&w.ir_type(), false)
                    .ok_or_else(|| self.refuse("has a primitive at a non-carrier width"))?;
                let a = self.scalar(&args[0], &t)?;
                let b = self.scalar(&args[1], &t)?;
                let op = match op {
                    ScalarCmp::Eq => ICmpOp::Eq,
                    ScalarCmp::Ult => ICmpOp::Ult,
                    ScalarCmp::Ule => ICmpOp::Ule,
                };
                Ok(Bound::Value(self.fb.icmp(op, t, a, b), Ty::Bool))
            }
            CarrierPrim::Bool(op) => {
                let a = self.scalar(&args[0], &Ty::Bool)?;
                let r = match op {
                    BoolOp::Not => self.not(a),
                    BoolOp::And => {
                        let b = self.scalar(&args[1], &Ty::Bool)?;
                        let f = self.fb.bool_const(false);
                        self.fb.select(Ty::Bool, a, b, f)
                    }
                    BoolOp::Or => {
                        let b = self.scalar(&args[1], &Ty::Bool)?;
                        let t = self.fb.bool_const(true);
                        self.fb.select(Ty::Bool, a, t, b)
                    }
                    BoolOp::Xor => {
                        let b = self.scalar(&args[1], &Ty::Bool)?;
                        let nb = self.not(b);
                        self.fb.select(Ty::Bool, a, nb, b)
                    }
                    BoolOp::Eq => {
                        let b = self.scalar(&args[1], &Ty::Bool)?;
                        let nb = self.not(b);
                        self.fb.select(Ty::Bool, a, b, nb)
                    }
                };
                Ok(Bound::Value(r, Ty::Bool))
            }
            // After `to_mono` a `Decidable` IS its `Bool`.
            CarrierPrim::Decide => Ok(Bound::Value(self.scalar(&args[1], &Ty::Bool)?, Ty::Bool)),
            CarrierPrim::Nat(op) => self.nat_prim(op, args),
        }
    }

    /// `¬b` — trust-ir has no `Bool` negation (`xor` needs an integer, `icmp`
    /// refuses `Bool`), so a `select`.
    fn not(&mut self, b: ValueId) -> ValueId {
        let f = self.fb.bool_const(false);
        let t = self.fb.bool_const(true);
        self.fb.select(Ty::Bool, b, f, t)
    }

    /// `is_zero(a ∸ b)` — `a ≤ b` under truncated subtraction.
    fn nat_le(&mut self, a: ValueId, b: ValueId) -> Result<ValueId, TrustIrError> {
        let d = self.nat_call("sub", vec![a, b])?;
        let z = self.nat_call("is_zero", vec![d])?;
        self.release(d)?;
        Ok(z)
    }

    fn nat_prim(&mut self, op: NatOp, args: &[IRArg]) -> Result<Bound, TrustIrError> {
        if let NatOp::OfUInt(w) = op {
            let t = carrier_ty(&w.ir_type(), false)
                .ok_or_else(|| self.refuse("has a primitive at a non-carrier width"))?;
            let v = self.scalar(&args[0], &t)?;
            let h = self.handle_of_scalar(v, &t)?;
            return Ok(Bound::Value(h, handle_ty()));
        }
        let (x, y) = (&args[0], &args[1]);
        let (lx, ly) = (self.literal_of(x), self.literal_of(y));
        if matches!(op, NatOp::Add | NatOp::Sub) {
            let role = if op == NatOp::Add { "add" } else { "sub" };
            let a = self.handle(x)?;
            let b = self.handle(y)?;
            let r = self.nat_call(role, vec![a.0, b.0])?;
            self.drop_temps(&[a, b])?;
            self.owned.push(r);
            return Ok(Bound::Value(r, handle_ty()));
        }
        // Comparisons: against a zero numeral nothing is allocated.
        let r = match (op, lx, ly) {
            (NatOp::Eq, _, Some(0)) | (NatOp::Le, _, Some(0)) => self.is_zero(x)?,
            (NatOp::Eq, Some(0), _) => self.is_zero(y)?,
            (NatOp::Le, Some(0), _) => self.fb.bool_const(true),
            (NatOp::Lt, _, Some(0)) => self.fb.bool_const(false),
            (NatOp::Lt, Some(0), _) => {
                let z = self.is_zero(y)?;
                self.not(z)
            }
            (NatOp::Le, ..) => {
                let a = self.handle(x)?;
                let b = self.handle(y)?;
                let z = self.nat_le(a.0, b.0)?;
                self.drop_temps(&[a, b])?;
                z
            }
            (NatOp::Lt, ..) => {
                let a = self.handle(x)?;
                let b = self.handle(y)?;
                let z = self.nat_le(b.0, a.0)?;
                self.drop_temps(&[a, b])?;
                self.not(z)
            }
            (NatOp::Eq, ..) => {
                let a = self.handle(x)?;
                let b = self.handle(y)?;
                let le = self.nat_le(a.0, b.0)?;
                let ge = self.nat_le(b.0, a.0)?;
                self.drop_temps(&[a, b])?;
                let f = self.fb.bool_const(false);
                self.fb.select(Ty::Bool, le, ge, f)
            }
            (NatOp::Add | NatOp::Sub | NatOp::OfUInt(_), ..) => {
                return Err(self.refuse("reached an unreachable Nat arm"))
            }
        };
        Ok(Bound::Value(r, Ty::Bool))
    }

    fn is_zero(&mut self, arg: &IRArg) -> Result<ValueId, TrustIrError> {
        let a = self.handle(arg)?;
        let z = self.nat_call("is_zero", vec![a.0])?;
        self.drop_temps(&[a])?;
        Ok(z)
    }

    fn literal(&mut self, lit: &IRLiteral) -> Result<Bound, TrustIrError> {
        let (ty, value) = match lit {
            IRLiteral::Bool(b) => return Ok(Bound::Value(self.fb.bool_const(*b), Ty::Bool)),
            IRLiteral::UInt8(v) => (Ty::U8, u64::from(*v)),
            IRLiteral::UInt16(v) => (Ty::U16, u64::from(*v)),
            IRLiteral::UInt32(v) => (Ty::U32, u64::from(*v)),
            IRLiteral::UInt64(v) => (Ty::U64, *v),
            IRLiteral::USize(v) => (Ty::U64, *v as u64),
            IRLiteral::NatBig(_) => {
                return Err(
                    self.refuse("has a Nat numeral above u64::MAX (no exported shim builds one)")
                )
            }
            IRLiteral::Float32(_) | IRLiteral::Float64(_) => {
                return Err(self.refuse("has a float literal"))
            }
        };
        let v = self.fb.iconst(ty.clone(), i128::from(value));
        self.literals.insert(v, value);
        Ok(Bound::Value(v, ty))
    }
}

fn expr_kind(expr: &IRExpr) -> &'static str {
    match expr {
        IRExpr::Ctor { .. } => "a constructor",
        IRExpr::Proj { .. } | IRExpr::SProj { .. } | IRExpr::UProj { .. } => "an object projection",
        IRExpr::Tag(_) => "a tag read",
        IRExpr::Box { .. } => "a box",
        IRExpr::Unbox { .. } => "an unbox",
        IRExpr::Lit(_) => "a literal",
        IRExpr::Apply { .. } => "a call",
        IRExpr::PartialApply { .. } => "a partial application (closure)",
        IRExpr::ClosureApply { .. } => "a closure application",
        IRExpr::IsShared(_) => "a sharing test",
        IRExpr::String(_) => "a string literal",
        IRExpr::Reset(_) | IRExpr::Reuse { .. } => "a constructor reuse",
    }
}

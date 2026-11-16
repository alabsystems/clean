// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A bounded checker for an emitted, homogeneous UInt32 boxed entry.
//!
//! This parses the ACTUAL module, independently of the wrapper generator:
//! decode every owned parameter, release each once after all reads, call the
//! specified scalar function with those values IN ORDER, encode its result,
//! and return that box. No extra instructions or implicit casts are admitted.
//!
//! This is NOT a translation certificate or a codegen license. In particular,
//! matching an external symbol and signature does not prove its implementation.
//! The conditional composition theorem below leaves its round-trip hypothesis
//! explicit. Instantiating it at the runtime still requires checked evidence
//! for the linked decoder/encoder, valid initialized UInt32 input boxes, one
//! transferred owned reference per parameter (including aliases), Release's
//! actual implementation, the scalar callee, and the target call ABI. Neither
//! the theorem nor this syntactic ownership check establishes those premises.
//! The pinned independent TV consumer also does not yet recheck this fragment.

use std::collections::BTreeSet;

use clean_kernel::{BinderInfo, Declaration, Expr, FVarId, Level, Name};
use trust_ir::inst::Inst;
use trust_ir::ty::Ty;
use trust_ir::{CallingConv, FuncId, Function, Module};

use crate::ReflectError;

/// The bounded closure-entry arity supported by this checker.
pub const MAX_UINT32_BOXED_ENTRY_ARGS: usize = 16;

/// Checked instruction choreography, with all semantic/runtime premises OPEN.
/// Fields are private so a caller cannot invent a successful parse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UInt32BoxedEntry {
    wrapper: FuncId,
    callee: FuncId,
    decoder: FuncId,
    encoder: FuncId,
    arity: usize,
}

impl UInt32BoxedEntry {
    #[must_use]
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// The exact functions read from this module. This is not an evidence
    /// binding: any later mutation requires checking the module again.
    #[must_use]
    pub fn functions(&self) -> [FuncId; 4] {
        [self.wrapper, self.callee, self.decoder, self.encoder]
    }

    /// The CONDITIONAL value-composition theorem for the checked call order:
    ///
    /// ```text
    /// forall (B S : Type) (decode : B -> S) (encode : S -> B),
    ///   (forall y, decode (encode y) = y) ->
    ///   forall (f : S^arity -> S) (x0 ... : B),
    ///     decode (encode (f (decode x0) ...)) = f (decode x0) ...
    /// ```
    /// Its proof is the round-trip HYPOTHESIS applied to the actual call's
    /// value, with no domain axioms. This deliberately proves no runtime/ABI
    /// premise and says nothing about Release or machine bytes. Callers must
    /// kernel-check the returned declaration; constructing it proves nothing.
    #[must_use]
    pub fn conditional_composition_theorem(&self, name: Name) -> Declaration {
        let id = |n| FVarId::new(n);
        let boxed = Expr::fvar(id(0));
        let scalar = Expr::fvar(id(1));
        let decode = Expr::fvar(id(2));
        let encode = Expr::fvar(id(3));
        let round_trip = Expr::fvar(id(4));
        let callee = Expr::fvar(id(5));
        let y = Expr::fvar(id(6));
        let eq = |a, b| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [scalar.clone(), a, b],
            )
        };
        let round_trip_ty = Expr::pi(
            BinderInfo::Default,
            scalar.clone(),
            eq(
                Expr::app(decode.clone(), Expr::app(encode.clone(), y.clone())),
                y,
            )
            .abstract_fvar(id(6)),
        );
        let mut binders = vec![
            (id(0), Expr::type_()),
            (id(1), Expr::type_()),
            (id(2), Expr::arrow(boxed.clone(), scalar.clone())),
            (id(3), Expr::arrow(scalar.clone(), boxed.clone())),
            (id(4), round_trip_ty),
            (
                id(5),
                (0..self.arity).fold(scalar.clone(), |acc, _| Expr::arrow(scalar.clone(), acc)),
            ),
        ];
        let mut args = Vec::with_capacity(self.arity);
        for i in 0..self.arity {
            // The parser bounds arity to 16 before this value can exist.
            let arg = id(7 + i as u64);
            binders.push((arg, boxed.clone()));
            args.push(Expr::app(decode.clone(), Expr::fvar(arg)));
        }
        let call = Expr::apps(callee, args);
        let mut statement = eq(
            Expr::app(decode, Expr::app(encode, call.clone())),
            call.clone(),
        );
        let mut proof = Expr::app(round_trip, call);
        for (var, ty) in binders.into_iter().rev() {
            statement = Expr::pi(
                BinderInfo::Default,
                ty.clone(),
                statement.abstract_fvar(var),
            );
            proof = Expr::lam(BinderInfo::Default, ty, proof.abstract_fvar(var));
        }
        Declaration::Theorem {
            name,
            level_params: vec![],
            type_: statement,
            value: proof,
        }
    }
}

fn wrong(reason: impl Into<String>) -> ReflectError {
    ReflectError::WrongEmission(format!("UInt32 boxed entry: {}", reason.into()))
}

fn function(module: &Module, id: FuncId) -> Result<&Function, ReflectError> {
    module
        .functions
        .iter()
        .find(|f| f.id == id)
        .ok_or_else(|| wrong(format!("missing function {id:?}")))
}

fn signature(
    module: &Module,
    function: &Function,
    params: &[Ty],
    result: Ty,
) -> Result<(), ReflectError> {
    let ty = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or_else(|| wrong("missing function type"))?;
    if ty.params != params
        || ty.returns != [result]
        || ty.is_vararg
        || function.calling_conv != CallingConv::C
    {
        return Err(wrong(format!("signature of `{}` disagrees", function.name)));
    }
    // An unrecorded target ABI is not an affirmative ABI proof. This checker
    // never licenses code, regardless of whether `ty.abi` is present.
    Ok(())
}

/// Parse one actual `Ptr^n -> Ptr` wrapper around the specified `U32^n -> U32`
/// definition. Unsupported signatures remain outside this bounded component;
/// a broken choreography in the requested shape is a detected wrong emission.
/// No module field, certificate, obligation or body gate is changed.
pub fn check_uint32_boxed_entry(
    module: &Module,
    wrapper: FuncId,
    callee: FuncId,
) -> Result<UInt32BoxedEntry, ReflectError> {
    let mut ids = BTreeSet::new();
    let mut symbols = BTreeSet::new();
    for f in &module.functions {
        if !ids.insert(f.id) || !symbols.insert(&f.name) {
            return Err(wrong("ambiguous function id or symbol"));
        }
    }
    let target = function(module, callee)?;
    let ty = module
        .func_types
        .get(target.ty.as_usize())
        .ok_or_else(|| wrong("missing scalar callee type"))?;
    let arity = ty.params.len();
    if arity == 0
        || arity > MAX_UINT32_BOXED_ENTRY_ARGS
        || ty.params != vec![Ty::U32; arity]
        || ty.returns != [Ty::U32]
    {
        return Err(ReflectError::unsupported(
            "boxed entry requires 1..=16 U32 arguments and a U32 result",
        ));
    }
    signature(module, target, &vec![Ty::U32; arity], Ty::U32)?;
    if target.is_declaration() || wrapper == callee {
        return Err(wrong("scalar callee must be a distinct definition"));
    }
    let entry = function(module, wrapper)?;
    signature(module, entry, &vec![Ty::Ptr; arity], Ty::Ptr)?;
    let [block] = entry.blocks.as_slice() else {
        return Err(wrong("wrapper must have exactly one block"));
    };
    if entry.entry != block.id
        || block.params.len() != arity
        || block.params.iter().any(|(_, ty)| *ty != Ty::Ptr)
        || block.body.len() != 2 * arity + 3
    {
        return Err(wrong("entry parameters or instruction count disagree"));
    }
    let mut values = BTreeSet::new();
    for (param, _) in &block.params {
        if !values.insert(*param) {
            return Err(wrong("duplicate parameter value"));
        }
    }
    for node in &block.body {
        for value in &node.results {
            if !values.insert(*value) {
                return Err(wrong("duplicate SSA result"));
            }
        }
    }
    let mut decoder = None;
    let mut decoded = Vec::with_capacity(arity);
    for (node, (param, _)) in block.body[..arity].iter().zip(&block.params) {
        let Inst::Call { callee: fid, args } = &node.inst else {
            return Err(wrong("expected a direct decoder call"));
        };
        let decode = function(module, *fid)?;
        signature(module, decode, &[Ty::Ptr], Ty::U32)?;
        if decode.name != "clean_unbox_uint32"
            || !decode.is_declaration()
            || args.as_slice() != [*param]
            || decoder.is_some_and(|old| old != *fid)
        {
            return Err(wrong("decoder identity or ordered argument disagrees"));
        }
        let [result] = node.results.as_slice() else {
            return Err(wrong("decoder must produce exactly one value"));
        };
        decoder = Some(*fid);
        decoded.push(*result);
    }
    for (node, (param, _)) in block.body[arity..2 * arity].iter().zip(&block.params) {
        let Inst::Release { ptr } = &node.inst else {
            return Err(wrong("every decoded input must be released exactly once"));
        };
        if ptr != param || !node.results.is_empty() {
            return Err(wrong("release target or result disagrees"));
        }
    }
    let call = &block.body[2 * arity];
    let Inst::Call { callee: fid, args } = &call.inst else {
        return Err(wrong("expected a direct scalar call"));
    };
    let [result] = call.results.as_slice() else {
        return Err(wrong("scalar call must produce exactly one value"));
    };
    if *fid != callee || args != &decoded {
        return Err(wrong("scalar callee or decoded argument order disagrees"));
    }
    let box_node = &block.body[2 * arity + 1];
    let Inst::Call {
        callee: encoder,
        args,
    } = &box_node.inst
    else {
        return Err(wrong("expected a direct encoder call"));
    };
    let encode = function(module, *encoder)?;
    signature(module, encode, &[Ty::U32], Ty::Ptr)?;
    if encode.name != "clean_box_uint32" || !encode.is_declaration() || args.as_slice() != [*result]
    {
        return Err(wrong("encoder identity or scalar result disagrees"));
    }
    let [boxed_result] = box_node.results.as_slice() else {
        return Err(wrong("encoder must produce exactly one box"));
    };
    let ret = &block.body[2 * arity + 2];
    let Inst::Return { values } = &ret.inst else {
        return Err(wrong("expected the final boxed return"));
    };
    if values.as_slice() != [*boxed_result] || !ret.results.is_empty() {
        return Err(wrong("return must transfer exactly the encoder's result"));
    }
    Ok(UInt32BoxedEntry {
        wrapper,
        callee,
        decoder: decoder.ok_or_else(|| wrong("missing decoder"))?,
        encoder: *encoder,
        arity,
    })
}

#[cfg(test)]
mod tests;

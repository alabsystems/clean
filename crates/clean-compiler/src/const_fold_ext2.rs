// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended constant folding pass (ext2) for L5IR: arithmetic, boolean, string,
//! comparison, constructor tag, projection, partial evaluation, dead branch
//! folding, and forward constant propagation with fixpoint iteration.
//!
//! Part of #3083 - Extensibility.

use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, VarId};
use std::collections::HashMap;

/// Configuration for the ext2 constant folding pass.
#[derive(Debug, Clone)]
pub(crate) struct ConstFoldExt2Config {
    pub(crate) fold_arithmetic: bool,
    pub(crate) fold_boolean: bool,
    pub(crate) fold_string: bool,
    pub(crate) fold_array: bool,
    pub(crate) fold_list: bool,
    pub(crate) fold_char: bool,
    pub(crate) fold_comparisons: bool,
    pub(crate) fold_bitwise: bool,
    pub(crate) fold_float: bool,
    pub(crate) fold_ctor_tag: bool,
    pub(crate) fold_projection: bool,
    pub(crate) fold_partial_eval: bool,
    pub(crate) fold_dead_branches: bool,
    pub(crate) propagate_constants: bool,
    pub(crate) max_string_length: usize,
    /// Maximum resolved `List` spine length to fold over. Bounds the
    /// [`resolve_list_spine`] walk (mirroring `max_string_length`): a spine
    /// longer than this — or a defensively-detected cycle — declines the fold.
    pub(crate) max_list_length: usize,
    pub(crate) max_iterations: usize,
}

impl Default for ConstFoldExt2Config {
    fn default() -> Self {
        Self {
            fold_arithmetic: true,
            fold_boolean: true,
            fold_string: true,
            fold_array: true,
            fold_list: true,
            fold_char: true,
            fold_comparisons: true,
            fold_bitwise: true,
            fold_float: true,
            fold_ctor_tag: true,
            fold_projection: true,
            fold_partial_eval: true,
            fold_dead_branches: true,
            propagate_constants: true,
            max_string_length: 4096,
            max_list_length: 4096,
            max_iterations: 10,
        }
    }
}

/// Statistics collected during the ext2 constant folding pass.
#[derive(Debug, Clone, Default)]
pub(crate) struct ConstFoldExt2Stats {
    pub(crate) arithmetic_folds: usize,
    pub(crate) boolean_folds: usize,
    pub(crate) string_folds: usize,
    pub(crate) array_folds: usize,
    pub(crate) list_folds: usize,
    pub(crate) char_folds: usize,
    pub(crate) comparison_folds: usize,
    pub(crate) bitwise_folds: usize,
    pub(crate) float_folds: usize,
    pub(crate) ctor_tag_folds: usize,
    pub(crate) projection_folds: usize,
    pub(crate) partial_eval_folds: usize,
    pub(crate) dead_branch_folds: usize,
    pub(crate) propagations: usize,
    pub(crate) iterations: usize,
}

impl ConstFoldExt2Stats {
    pub(crate) fn total_folds(&self) -> usize {
        self.arithmetic_folds
            + self.boolean_folds
            + self.string_folds
            + self.array_folds
            + self.list_folds
            + self.char_folds
            + self.comparison_folds
            + self.bitwise_folds
            + self.float_folds
            + self.ctor_tag_folds
            + self.projection_folds
            + self.partial_eval_folds
            + self.dead_branch_folds
    }
    pub(crate) fn merge(&mut self, o: &Self) {
        self.arithmetic_folds += o.arithmetic_folds;
        self.boolean_folds += o.boolean_folds;
        self.string_folds += o.string_folds;
        self.array_folds += o.array_folds;
        self.list_folds += o.list_folds;
        self.char_folds += o.char_folds;
        self.comparison_folds += o.comparison_folds;
        self.bitwise_folds += o.bitwise_folds;
        self.float_folds += o.float_folds;
        self.ctor_tag_folds += o.ctor_tag_folds;
        self.projection_folds += o.projection_folds;
        self.partial_eval_folds += o.partial_eval_folds;
        self.dead_branch_folds += o.dead_branch_folds;
        self.propagations += o.propagations;
    }
}

// -- Known-value tracking (constant propagation) -----------------------------

/// A compile-time-known value.
#[derive(Clone, Debug)]
pub(crate) enum KnownVal2 {
    Lit(IRLiteral),
    Str(String),
    Ctor {
        tag: u32,
        info: CtorInfo,
        args: Vec<IRArg>,
    },
    Bool(bool),
    /// A statically-known array literal: the constructor used to (re)build it,
    /// plus its element arguments in order. Tracked so `Array.size` /
    /// `Array.get` / `Array.set` can be folded the same way `String.*` ops fold
    /// over a known `Str`.
    Array {
        info: CtorInfo,
        elems: Vec<IRArg>,
    },
    /// A statically-known `List` cons-spine node, recorded from a `List.nil` or
    /// `List.cons` constructor. Tracked so the `List.*` accessors can be folded
    /// against the known spine the same way `Array.*` folds over a known
    /// `Array.mk`.
    ///
    /// Unlike an `Array`, a `List` is a *linked spine*: each `List.cons` node is
    /// a separate IR constructor whose tail is a variable bound to the next node.
    /// We therefore record one node at a time — `List.nil` (the empty spine) or a
    /// `List.cons` carrying its head element and a reference to the tail node —
    /// and resolve the full spine by walking the tail chain through the
    /// [`PropagationEnv`] at fold time (see [`resolve_list_spine`]). A tail that
    /// does not resolve to a tracked nil/cons node makes the spine non-ground and
    /// declines the fold.
    ///
    /// `info` is the constructor used to (re)build the node (`List.nil` /
    /// `List.cons`). For a `List.cons` node, `head` is the element argument and
    /// `tail` is the argument referencing the next spine node; for `List.nil`
    /// both are `None`.
    List {
        info: CtorInfo,
        head: Option<IRArg>,
        tail: Option<IRArg>,
    },
}

/// Tracks known variable bindings for constant propagation.
pub(crate) struct PropagationEnv {
    bindings: HashMap<VarId, KnownVal2>,
}

impl PropagationEnv {
    pub(crate) fn new() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }
    pub(crate) fn insert(&mut self, var: VarId, val: KnownVal2) {
        self.bindings.insert(var, val);
    }
    pub(crate) fn get(&self, var: VarId) -> Option<&KnownVal2> {
        self.bindings.get(&var)
    }
    fn clone_scope(&self) -> Self {
        Self {
            bindings: self.bindings.clone(),
        }
    }

    fn record_expr(&mut self, var: VarId, expr: &IRExpr) {
        match expr {
            IRExpr::Lit(IRLiteral::Bool(b)) => {
                self.insert(var, KnownVal2::Bool(*b));
            }
            IRExpr::Lit(lit) => {
                self.insert(var, KnownVal2::Lit(lit.clone()));
            }
            IRExpr::String(s) => {
                self.insert(var, KnownVal2::Str(s.clone()));
            }
            IRExpr::Ctor { info, args } if is_array_ctor(&info.name.to_string()) => {
                // `Array.mk elems...` is a statically-known array literal; track
                // its elements so `Array.size` / `Array.get` / `Array.set` fold.
                self.insert(
                    var,
                    KnownVal2::Array {
                        info: info.clone(),
                        elems: args.clone(),
                    },
                );
            }
            IRExpr::Ctor { info, args: _ } if is_list_nil_ctor(&info.name.to_string()) => {
                // `List.nil` is the empty spine. It carries no elements (only an
                // erased/implicit type parameter, if anything), so head/tail are
                // `None`. Tracked so `List.length`/`List.isEmpty`/... fold.
                self.insert(
                    var,
                    KnownVal2::List {
                        info: info.clone(),
                        head: None,
                        tail: None,
                    },
                );
            }
            IRExpr::Ctor { info, args } if is_list_cons_ctor(&info.name.to_string()) => {
                // `List.cons head tail`: a spine node. The tail is the LAST
                // argument and the head the second-to-last in both the kernel
                // term layout (`[type, head, tail]`) and the type-erased IR
                // layout (`[head, tail]`); see [`KnownVal2::List`]. Record only a
                // well-formed node (at least head+tail present), so a malformed
                // arg list leaves the binding untracked and declines the fold.
                if let Some((head, tail)) = list_cons_head_tail(args) {
                    self.insert(
                        var,
                        KnownVal2::List {
                            info: info.clone(),
                            head: Some(head),
                            tail: Some(tail),
                        },
                    );
                }
            }
            IRExpr::Ctor { info, args } => {
                self.insert(
                    var,
                    KnownVal2::Ctor {
                        tag: info.tag,
                        info: info.clone(),
                        args: args.clone(),
                    },
                );
            }
            _ => {}
        }
    }

    fn get_arg_u64(&self, arg: &IRArg) -> Option<u64> {
        match arg {
            IRArg::Var(v) => match self.get(*v)? {
                KnownVal2::Lit(l) => extract_u64(l),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }
    /// Look up the raw typed literal bound to an argument, if known. Unlike
    /// [`Self::get_arg_u64`] this preserves the literal's exact variant/width,
    /// which bitwise and float folds need to compute and re-tag correctly.
    fn get_arg_lit(&self, arg: &IRArg) -> Option<&IRLiteral> {
        match arg {
            IRArg::Var(v) => match self.get(*v)? {
                KnownVal2::Lit(l) => Some(l),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }
    fn get_arg_bool(&self, arg: &IRArg) -> Option<bool> {
        match arg {
            IRArg::Var(v) => match self.get(*v)? {
                KnownVal2::Bool(b) => Some(*b),
                KnownVal2::Lit(IRLiteral::Bool(b)) => Some(*b),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }
    fn get_arg_string(&self, arg: &IRArg) -> Option<&str> {
        match arg {
            IRArg::Var(v) => match self.get(*v)? {
                KnownVal2::Str(s) => Some(s),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }
    /// Resolve an argument to a statically-known array `(ctor, elems)`, or
    /// `None` if the argument is not bound to a tracked `Array.mk` literal.
    fn get_arg_array(&self, arg: &IRArg) -> Option<(&CtorInfo, &[IRArg])> {
        match arg {
            IRArg::Var(v) => match self.get(*v)? {
                KnownVal2::Array { info, elems } => Some((info, elems)),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }
    /// Resolve an argument to a statically-known `List` spine node, or `None` if
    /// the argument is not bound to a tracked `List.nil`/`List.cons` node. The
    /// returned `head`/`tail` are `None` for a `nil` node and `Some` for a `cons`
    /// node (see [`KnownVal2::List`]).
    fn get_arg_list(&self, arg: &IRArg) -> Option<(&CtorInfo, Option<&IRArg>, Option<&IRArg>)> {
        match arg {
            IRArg::Var(v) => match self.get(*v)? {
                KnownVal2::List { info, head, tail } => Some((info, head.as_ref(), tail.as_ref())),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }

    fn get_tag(&self, var: VarId) -> Option<u32> {
        match self.get(var)? {
            KnownVal2::Ctor { tag, .. } => Some(*tag),
            _ => None,
        }
    }
    fn get_ctor_arg(&self, var: VarId, idx: u32) -> Option<&IRArg> {
        match self.get(var)? {
            KnownVal2::Ctor { args, .. } => args.get(idx as usize),
            _ => None,
        }
    }
}

// -- Pure folding helpers ----------------------------------------------------

/// Whether a constructor name denotes the `Array` literal constructor.
///
/// In Lean 4 `Array α` is a single-constructor structure whose constructor is
/// `Array.mk`; the const-fold tracks its elements so the `Array.*` accessors can
/// be folded against the known literal.
fn is_array_ctor(name: &str) -> bool {
    name == "Array.mk"
}

/// Whether a constructor name denotes the empty-`List` constructor `List.nil`.
fn is_list_nil_ctor(name: &str) -> bool {
    name == "List.nil"
}

/// Whether a constructor name denotes the `List` cons constructor `List.cons`.
fn is_list_cons_ctor(name: &str) -> bool {
    name == "List.cons"
}

/// Extract the `(head, tail)` arguments of a `List.cons` node from its IR
/// constructor argument list.
///
/// `List.cons` is `{α : Type u} → α → List α → List α`: the **tail** is always
/// the last argument and the **head** the second-to-last, in both the kernel
/// term layout (`[type, head, tail]`, matched by the native reducer in
/// `clean-kernel`) and the type-erased IR layout (`[head, tail]`). Requiring at
/// least two arguments and slicing from the end is exact for both. Returns
/// `None` for a malformed node (fewer than two arguments), which declines the
/// fold rather than guess a layout.
fn list_cons_head_tail(args: &[IRArg]) -> Option<(IRArg, IRArg)> {
    if args.len() < 2 {
        return None;
    }
    let tail = args[args.len() - 1].clone();
    let head = args[args.len() - 2].clone();
    Some((head, tail))
}

fn extract_u64(lit: &IRLiteral) -> Option<u64> {
    match lit {
        IRLiteral::UInt64(v) => Some(*v),
        IRLiteral::UInt32(v) => Some(*v as u64),
        IRLiteral::UInt16(v) => Some(*v as u64),
        IRLiteral::UInt8(v) => Some(*v as u64),
        IRLiteral::USize(v) => Some(*v as u64),
        _ => None,
    }
}

/// Greatest common divisor (Euclidean), total on all `u64` inputs.
///
/// Matches Lean's `Nat.gcd` and the elaborator simproc `Nat.reduceGcd`:
/// `gcd(a, 0) = a`, `gcd(0, b) = b`, and `gcd(0, 0) = 0`.
fn nat_gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Fold a binary `Nat`/`Int` arithmetic operation on two closed operands.
///
/// AUTHORITATIVE SEMANTICS. Both `Nat` and `Int` are **unbounded** (bignum) in
/// the kernel reducer (`TypeChecker::reduce_nat`, `crates/clean-kernel`) and the
/// runtime — they never wrap or saturate at a machine width:
///
/// * `Nat` is a non-negative bignum: `Nat.sub` is *truncated* subtraction
///   (floored at `0`, NOT machine-saturating); `Nat.add`/`Nat.mul`/`Nat.pow`
///   are exact (the kernel computes them over `u128` and promotes to `BigNat`).
/// * `Int` is a signed bignum: `Int.add`/`Int.sub`/`Int.mul` are exact, with no
///   two's-complement wrap.
///
/// Const-fold here is restricted to operands that fit in a machine `u64` (the
/// only integer literals the IR carries are fixed-width `UInt*`/`USize`, widened
/// via `extract_u64`; the `Int.*` cases reinterpret that word as `i64`). Because
/// a *wrong* fold is a miscompilation, every arm computes the **exact** kernel
/// value when it is representable and otherwise **declines** (`None`): it must
/// never silently wrap/saturate a result the kernel would have computed
/// differently. The callers leave the original call untouched on `None`.
pub(crate) fn fold_arith(op: &str, lhs: u64, rhs: u64) -> Option<u64> {
    match op {
        // `Nat` is an unbounded non-negative bignum. We can only represent
        // results that fit in `u64`, so add/mul DECLINE on overflow (rather than
        // wrap) — the kernel would have produced a `BigNat` we cannot encode.
        "Nat.add" => lhs.checked_add(rhs),
        // `Nat.sub` is truncated subtraction: `a - b = 0` when `b > a`. This is
        // the kernel's `saturating_sub` flooring at 0 (NOT a machine clamp at
        // `u64::MAX`), and is exact for all `u64` inputs.
        "Nat.sub" => Some(lhs.saturating_sub(rhs)),
        "Nat.mul" => lhs.checked_mul(rhs),
        // Lean `Nat` division and modulus are *total*: division by zero yields
        // `0` and modulus by zero yields the dividend. This matches both the
        // elaborator simprocs (`Nat.reduceDiv` / `Nat.reduceMod`) and the
        // runtime (`native_eval::eval_int_binop`), so folding the zero-divisor
        // edge cases is sound rather than merely conservative.
        "Nat.div" => Some(lhs.checked_div(rhs).unwrap_or(0)),
        "Nat.mod" => Some(if rhs == 0 { lhs } else { lhs % rhs }),
        // Exponentiation: the exponent must fit in `u32` and the result must not
        // overflow `u64`; otherwise decline (matches `Nat.reducePow`). `Nat.pow`
        // is `0^0 = 1` via `u64::pow(0)`.
        "Nat.pow" => u32::try_from(rhs).ok().and_then(|e| lhs.checked_pow(e)),
        // GCD / max / min are total on all inputs.
        "Nat.gcd" => Some(nat_gcd(lhs, rhs)),
        "Nat.max" => Some(lhs.max(rhs)),
        "Nat.min" => Some(lhs.min(rhs)),
        // `Nat` bitwise AND/OR/XOR. `Nat` is a non-negative unbounded bignum, so
        // the kernel's `reduce_nat_land` / `reduce_nat_lor` / `reduce_nat_lxor`
        // (`crates/clean-kernel/src/env/native_reducers_arith.rs`) compute plain
        // `a & b` / `a | b` / `a ^ b` over the bignum. Because both operands are
        // non-negative and fit in `u64`, the result also fits in `u64` (bitwise
        // never produces a value larger than the larger operand), so the `u64`
        // computation is *exact* — no width truncation, no decline needed. The
        // kernel registers XOR under the Lean name `Nat.xor` (the `NAT_LXOR`
        // constant), so that is the op string we match here.
        "Nat.land" => Some(lhs & rhs),
        "Nat.lor" => Some(lhs | rhs),
        "Nat.xor" => Some(lhs ^ rhs),
        // `Int` is an unbounded signed bignum; it does NOT wrap. We model the
        // operand as the `i64` reinterpretation of the carried word, and fold
        // only when the *exact* mathematical result is representable in `i64`.
        // `checked_*` returns `None` on signed overflow, so we DECLINE rather
        // than emit a two's-complement-wrapped value the kernel never produces.
        "Int.add" => Some((lhs as i64).checked_add(rhs as i64)? as u64),
        "Int.sub" => Some((lhs as i64).checked_sub(rhs as i64)? as u64),
        "Int.mul" => Some((lhs as i64).checked_mul(rhs as i64)? as u64),
        // `Int` division/modulus by zero is left untouched (conservative): the
        // signed total-vs-trap semantics are not pinned by an elaborator
        // simproc here, so we decline rather than risk a divergent result.
        // `checked_div`/`checked_rem` also decline the `i64::MIN / -1` overflow
        // (true quotient `2^63` is not `i64`-representable) instead of wrapping.
        "Int.div" if rhs != 0 => Some((lhs as i64).checked_div(rhs as i64)? as u64),
        "Int.mod" if rhs != 0 => Some((lhs as i64).checked_rem(rhs as i64)? as u64),
        // `Int` shifts model the (signed) i64 representation used by the other
        // `Int.*` cases.
        //   * `shiftLeft` is multiplication by `2^n`; an exact unbounded result
        //     can exceed `i64`, so we fold only when no significant bit is
        //     shifted out (else DECLINE — never wrap). A shift `>= 64` keeps
        //     only the all-zero / all-`-1` operands (their value is unchanged).
        //   * `shiftRight` is `a / 2^n` (arithmetic, sign-filling) and is always
        //     representable; `>= 64` collapses to the sign fill (`0` / `-1`).
        "Int.shiftLeft" | "Int.shiftL" => {
            let a = lhs as i64;
            if rhs >= 64 {
                // Only `0` survives a >=64-bit left shift without losing bits
                // (its exact result is `0`); any other value would overflow.
                (a == 0).then_some(0)
            } else {
                a.checked_shl(rhs as u32).and_then(|shifted| {
                    // `checked_shl` only guards the shift *count*, not value
                    // overflow. Require the shift to be exactly invertible so
                    // the folded `i64` equals the true unbounded product.
                    ((shifted >> rhs) == a).then_some(shifted as u64)
                })
            }
        }
        "Int.shiftRight" | "Int.shiftR" => Some(if rhs >= 64 {
            ((lhs as i64) >> 63) as u64
        } else {
            ((lhs as i64) >> rhs) as u64
        }),
        // `Int.land` / `Int.lor` / `Int.xor` / `Int.lnot` are deliberately NOT
        // folded here (they fall through to `None`, leaving the call untouched).
        // Two reasons, both grounded in the decline-rather-than-guess rule:
        //   1. The kernel has *no* native reducer for signed bitwise (there is
        //      no `reduce_int_land`/`reduce_int_lor`/`reduce_int_xor`/`Int.lnot`
        //      in `clean-kernel`), so there is no authoritative result to match.
        //   2. `Int` is an unbounded signed bignum using *infinite* two's-
        //      complement, so a negative operand's bit pattern is not faithfully
        //      represented by a fixed 64-bit word. `(-1 : Int).land x` would need
        //      an all-ones infinite prefix; folding it through `i64` would emit a
        //      width-truncated value the kernel never produces. Rather than fold
        //      only the non-negative sub-case (a foot-gun once the IR gains true
        //      `Int` literals), we decline `Int` bitwise entirely.
        _ => None,
    }
}

/// Fold the unary `Int.abs` / `Int.natAbs`.
///
/// `Int` is an unbounded signed bignum, so `Int.abs`/`Int.natAbs` are total and
/// always non-negative. We model the operand as the `i64` reinterpretation of
/// the carried word and fold only when the exact `|a|` is representable: for
/// `a == i64::MIN` the true result is `2^63`, which has no positive `i64`
/// representation, so we DECLINE (`checked_abs` returns `None`) rather than
/// `wrapping_abs` back to the negative `i64::MIN` — a wrong fold the kernel
/// never produces.
pub(crate) fn fold_int_abs(op: &str, arg: u64) -> Option<u64> {
    match op {
        "Int.abs" | "Int.natAbs" => Some((arg as i64).checked_abs()? as u64),
        _ => None,
    }
}

pub(crate) fn fold_bool(op: &str, args: &[IRArg], env: &PropagationEnv) -> Option<bool> {
    match op {
        "Bool.and" | "Bool.true.and" if args.len() == 2 => {
            Some(env.get_arg_bool(&args[0])? && env.get_arg_bool(&args[1])?)
        }
        "Bool.or" | "Bool.true.or" if args.len() == 2 => {
            Some(env.get_arg_bool(&args[0])? || env.get_arg_bool(&args[1])?)
        }
        "Bool.not" if args.len() == 1 => Some(!env.get_arg_bool(&args[0])?),
        // Exclusive-or and (in)equality of booleans are total. `Bool.xor`,
        // `Bool.beq`, and `Bool.bne` all reduce to standard bit logic on the
        // two known operands.
        "Bool.xor" if args.len() == 2 => {
            Some(env.get_arg_bool(&args[0])? ^ env.get_arg_bool(&args[1])?)
        }
        "Bool.beq" if args.len() == 2 => {
            Some(env.get_arg_bool(&args[0])? == env.get_arg_bool(&args[1])?)
        }
        "Bool.bne" if args.len() == 2 => {
            Some(env.get_arg_bool(&args[0])? != env.get_arg_bool(&args[1])?)
        }
        _ => None,
    }
}

/// Fold a closed `String.*` operation to a constant IR expression.
///
/// CORRECTNESS CONTRACT (exactness-or-decline). Const-fold must be
/// observationally equivalent to the kernel reduction or it is a
/// miscompilation. Every arm below mirrors the corresponding native reducer in
/// `clean-kernel/src/env/native_reducers_string.rs` and
/// `clean-kernel/src/env/native_reducers_string_ext.rs` (search/replace/trim/
/// compare) *byte-for-byte*: same
/// position semantics, same out-of-bounds behaviour. Lean `String` is UTF-8 and
/// `String.Pos` positions are **byte** offsets, NOT char indices, so the
/// byte-position ops (`get`/`front`/`atEnd`/`extract`) index into the UTF-8
/// bytes exactly as the kernel does; the character-count ops (`take`/`drop`)
/// operate on `chars()`. When the literals available at fold time cannot
/// reproduce the kernel value exactly (e.g. an invalid code point for
/// `singleton`, or a non-boundary byte slice for `extract`), we DECLINE
/// (`None`) and leave the call to the kernel rather than approximate.
///
/// A `Char` value is materialized exactly as `to_ir_ext::lower_char_literal`
/// does — `IRExpr::Lit(IRLiteral::UInt32(code_point))` — so a folded
/// `String.get`/`String.front` is bit-identical to a Char literal the lowerer
/// would have emitted.
pub(crate) fn fold_string(
    op: &str,
    args: &[IRArg],
    env: &PropagationEnv,
    max_len: usize,
) -> Option<IRExpr> {
    match op {
        "String.append" if args.len() == 2 => {
            let (a, b) = (env.get_arg_string(&args[0])?, env.get_arg_string(&args[1])?);
            if a.len().checked_add(b.len())? > max_len {
                return None;
            }
            Some(IRExpr::String(format!("{a}{b}")))
        }
        "String.length" if args.len() == 1 => Some(IRExpr::Lit(IRLiteral::UInt64(
            env.get_arg_string(&args[0])?.len() as u64,
        ))),
        "String.isEmpty" if args.len() == 1 => Some(IRExpr::Lit(IRLiteral::Bool(
            env.get_arg_string(&args[0])?.is_empty(),
        ))),
        // `String.take : String → Nat → String` — first `n` CHARACTERS.
        // Mirrors `reduce_string_take`: `s.chars().take(n).collect()`.
        "String.take" if args.len() == 2 => {
            let s = env.get_arg_string(&args[0])?;
            let n = usize::try_from(env.get_arg_u64(&args[1])?).ok()?;
            let result: String = s.chars().take(n).collect();
            (result.len() <= max_len).then_some(IRExpr::String(result))
        }
        // `String.drop : String → Nat → String` — drop first `n` CHARACTERS.
        // Mirrors `reduce_string_drop`: `s.chars().skip(n).collect()`.
        "String.drop" if args.len() == 2 => {
            let s = env.get_arg_string(&args[0])?;
            let n = usize::try_from(env.get_arg_u64(&args[1])?).ok()?;
            let result: String = s.chars().skip(n).collect();
            (result.len() <= max_len).then_some(IRExpr::String(result))
        }
        // `String.toLower : String → String`. Mirrors `reduce_string_to_lower`:
        // `s.to_lowercase()` (full Unicode lowercasing, identical to the kernel).
        "String.toLower" if args.len() == 1 => {
            let result = env.get_arg_string(&args[0])?.to_lowercase();
            (result.len() <= max_len).then_some(IRExpr::String(result))
        }
        // `String.toUpper : String → String`. Mirrors `reduce_string_to_upper`:
        // `s.to_uppercase()`.
        "String.toUpper" if args.len() == 1 => {
            let result = env.get_arg_string(&args[0])?.to_uppercase();
            (result.len() <= max_len).then_some(IRExpr::String(result))
        }
        // `String.singleton : Char → String`. Mirrors `reduce_string_singleton`:
        // the `Char` arg is its code point (a `UInt32` literal in the IR, per
        // `lower_char_literal`); decline if it is not a valid scalar value, just
        // as the kernel's `get_char_val`/`char::from_u32` returns `None`.
        "String.singleton" if args.len() == 1 => {
            let code = u32::try_from(env.get_arg_u64(&args[0])?).ok()?;
            let c = char::from_u32(code)?;
            Some(IRExpr::String(c.to_string()))
        }
        // `String.get : String → String.Pos → Char` — `String.Pos` is a BYTE
        // offset. Mirrors `reduce_string_get`: out-of-range (`pos >= len`) or a
        // pos landing inside a multi-byte char yields the default `'\0'`
        // (`Char.mk 0`); otherwise the char starting at that byte. The result is
        // a `Char`, materialized as a `UInt32` code point (see `lower_char_literal`).
        "String.get" if args.len() == 2 => {
            let s = env.get_arg_string(&args[0])?;
            let byte_pos = usize::try_from(env.get_arg_u64(&args[1])?).ok()?;
            // `reduce_string_get` returns `mk_char_expr('\0')` when out of range,
            // and `s[byte_pos..].chars().next()?` otherwise. Slicing at a
            // non-boundary byte would panic in the kernel's `s[byte_pos..]`, so
            // const-fold declines that case (leaving it to the kernel) rather
            // than risk diverging; the in-bounds boundary case is exact.
            if byte_pos >= s.len() {
                return Some(IRExpr::Lit(IRLiteral::UInt32(0)));
            }
            if !s.is_char_boundary(byte_pos) {
                return None;
            }
            let c = s[byte_pos..].chars().next()?;
            Some(IRExpr::Lit(IRLiteral::UInt32(c as u32)))
        }
        // `String.front : String → Char`. Mirrors `reduce_string_front`:
        // `s.chars().next().unwrap_or('\0')`, as a `UInt32` code point.
        "String.front" if args.len() == 1 => {
            let s = env.get_arg_string(&args[0])?;
            let c = s.chars().next().unwrap_or('\0');
            Some(IRExpr::Lit(IRLiteral::UInt32(c as u32)))
        }
        // `String.atEnd : String → String.Pos → Bool` (BYTE offset). Mirrors
        // `reduce_string_at_end`: `byte_pos >= s.len()`.
        "String.atEnd" if args.len() == 2 => {
            let s = env.get_arg_string(&args[0])?;
            let byte_pos = usize::try_from(env.get_arg_u64(&args[1])?).ok()?;
            Some(IRExpr::Lit(IRLiteral::Bool(byte_pos >= s.len())))
        }
        // `String.extract : String → String.Pos → String.Pos → String` (BYTE
        // offsets). Mirrors `reduce_string_extract` exactly: clamp both bounds to
        // `s.len()`, empty string when `start >= stop`, and DECLINE (`None`) when
        // either clamped bound is not on a char boundary (the kernel returns
        // `None` there too, so the call is left to the kernel).
        "String.extract" if args.len() == 3 => {
            let s = env.get_arg_string(&args[0])?;
            let start = std::cmp::min(usize::try_from(env.get_arg_u64(&args[1])?).ok()?, s.len());
            let stop = std::cmp::min(usize::try_from(env.get_arg_u64(&args[2])?).ok()?, s.len());
            if start >= stop {
                return Some(IRExpr::String(String::new()));
            }
            if !s.is_char_boundary(start) || !s.is_char_boundary(stop) {
                return None;
            }
            let result = s[start..stop].to_owned();
            (result.len() <= max_len).then_some(IRExpr::String(result))
        }
        // `String.startsWith : String → String → Bool`. Mirrors
        // `reduce_string_starts_with`: `s.starts_with(prefix)` (total, exact).
        "String.startsWith" if args.len() == 2 => {
            let s = env.get_arg_string(&args[0])?;
            let prefix = env.get_arg_string(&args[1])?;
            Some(IRExpr::Lit(IRLiteral::Bool(s.starts_with(prefix))))
        }
        // `String.endsWith : String → String → Bool`. Mirrors
        // `reduce_string_ends_with`: `s.ends_with(suffix)` (total, exact).
        "String.endsWith" if args.len() == 2 => {
            let s = env.get_arg_string(&args[0])?;
            let suffix = env.get_arg_string(&args[1])?;
            Some(IRExpr::Lit(IRLiteral::Bool(s.ends_with(suffix))))
        }
        // `String.containsSubstr : String → String → Bool`. Mirrors
        // `reduce_string_contains`: `s.contains(needle)` (total, exact). The Lean
        // name is `String.containsSubstr` (substring containment), NOT the
        // char-membership `String.contains`, matching the kernel's registered
        // name (`STRING_CONTAINS`).
        "String.containsSubstr" if args.len() == 2 => {
            let s = env.get_arg_string(&args[0])?;
            let needle = env.get_arg_string(&args[1])?;
            Some(IRExpr::Lit(IRLiteral::Bool(s.contains(needle))))
        }
        // `String.isPrefixOf : String → String → Bool`. Mirrors
        // `reduce_string_is_prefix_of`: the FIRST argument is the prefix and the
        // SECOND the haystack, so the result is `s.starts_with(prefix)` with the
        // operands read in that order (NOT swapped like `String.startsWith`).
        "String.isPrefixOf" if args.len() == 2 => {
            let prefix = env.get_arg_string(&args[0])?;
            let s = env.get_arg_string(&args[1])?;
            Some(IRExpr::Lit(IRLiteral::Bool(s.starts_with(prefix))))
        }
        // `String.replace : String → String → String → String`. Mirrors
        // `reduce_string_replace`: `s.replace(pat, rep)` (total, exact). Length-
        // guarded against `max_len` like `append`/`extract` so a pathological
        // blow-up declines rather than allocating an unbounded literal.
        "String.replace" if args.len() == 3 => {
            let s = env.get_arg_string(&args[0])?;
            let pat = env.get_arg_string(&args[1])?;
            let rep = env.get_arg_string(&args[2])?;
            let result = s.replace(pat, rep);
            (result.len() <= max_len).then_some(IRExpr::String(result))
        }
        // `String.trimLeft : String → String`. Mirrors `reduce_string_trim_left`:
        // `s.trim_start()` (remove leading whitespace). The result is a substring
        // of `s`, so it is always within `max_len` once `s` was.
        "String.trimLeft" if args.len() == 1 => Some(IRExpr::String(
            env.get_arg_string(&args[0])?.trim_start().to_owned(),
        )),
        // `String.trimRight : String → String`. Mirrors `reduce_string_trim_right`:
        // `s.trim_end()` (remove trailing whitespace).
        "String.trimRight" if args.len() == 1 => Some(IRExpr::String(
            env.get_arg_string(&args[0])?.trim_end().to_owned(),
        )),
        // `String.substrEq : String → Nat → String → Nat → Nat → Bool`. Mirrors
        // `reduce_string_substr_eq` *exactly*: byte-offset substring comparison.
        // Out-of-bounds (`off + len > len`) is `false`; a non-char-boundary
        // offset/end DECLINES (`None`, as the kernel does), leaving the call to
        // the kernel rather than risk a divergent slice. The kernel uses plain
        // `off + len`; we use `checked_add` and DECLINE on overflow (the only
        // observable difference would be a kernel panic, never a `Bool` value, so
        // declining is sound).
        "String.substrEq" if args.len() == 5 => {
            let s1 = env.get_arg_string(&args[0])?;
            let off1 = usize::try_from(env.get_arg_u64(&args[1])?).ok()?;
            let s2 = env.get_arg_string(&args[2])?;
            let off2 = usize::try_from(env.get_arg_u64(&args[3])?).ok()?;
            let len = usize::try_from(env.get_arg_u64(&args[4])?).ok()?;
            let end1 = off1.checked_add(len)?;
            let end2 = off2.checked_add(len)?;
            if end1 > s1.len() || end2 > s2.len() {
                return Some(IRExpr::Lit(IRLiteral::Bool(false)));
            }
            if !s1.is_char_boundary(off1)
                || !s1.is_char_boundary(end1)
                || !s2.is_char_boundary(off2)
                || !s2.is_char_boundary(end2)
            {
                return None;
            }
            Some(IRExpr::Lit(IRLiteral::Bool(
                s1[off1..end1] == s2[off2..end2],
            )))
        }
        _ => None,
    }
}

/// Fold a closed `Char.*` operation to a constant IR expression.
///
/// CORRECTNESS CONTRACT (exactness-or-decline). A `Char` in the L5IR is its
/// Unicode scalar value as a `UInt32` code point — exactly what
/// `to_ir_ext::lower_char_literal` emits and what the `String.get` / `String.front`
/// / `String.singleton` folds already produce and consume. Every arm below
/// mirrors the corresponding native reducer in
/// `clean-kernel/src/env/native_reducers_char.rs` *exactly*, including the
/// kernel's specific choices (`Char.isDigit` is ASCII-only `'0'..='9'`,
/// `Char.toLower`/`toUpper` use ASCII fast-path then first-char Unicode mapping).
/// When the operand cannot reproduce the kernel value exactly we DECLINE
/// (`None`) and leave the call to the kernel.
///
/// Operand decoding mirrors the kernel's `get_char_val`: the code point is read
/// via [`PropagationEnv::get_arg_u64`] (the IR carries the `Char` as a `UInt32`,
/// widened to `u64`) and re-validated with `char::from_u32`, which declines a
/// non-scalar value just as the kernel's `get_char_val` returns `None`.
///
/// Result tagging matches the lowerer and the other folds:
/// * a `Char` result is materialized as `IRLiteral::UInt32(code_point)` (the
///   `lower_char_literal` shape), so it is bit-identical to a Char literal;
/// * a `Nat` result (`Char.toNat`/`Char.val`) is `IRLiteral::UInt64`, matching
///   how `String.length` materializes the kernel's `Nat` result;
/// * a `Bool` result is `IRLiteral::Bool`.
///
/// The decidable ops (`Char.decEq`/`Char.decLe`) are deliberately NOT folded:
/// their kernel result is a `Decidable` *constructor* (`isTrue`/`isFalse`
/// carrying a proof), not a scalar literal a single [`IRExpr`] can represent, so
/// we decline rather than guess a constructor layout.
pub(crate) fn fold_char(op: &str, args: &[IRArg], env: &PropagationEnv) -> Option<IRExpr> {
    /// Decode an argument as a `Char` (its `UInt32` code point), declining on a
    /// non-scalar value exactly as the kernel's `get_char_val` does.
    fn arg_char(env: &PropagationEnv, arg: &IRArg) -> Option<char> {
        char::from_u32(u32::try_from(env.get_arg_u64(arg)?).ok()?)
    }
    match op {
        // `Char.ofNat : Nat → Char`. Mirrors `reduce_char_of_nat`: read the `Nat`
        // operand, truncate to `u32` (the kernel's `n as u32`), and map an invalid
        // scalar value to `'\0'` via `char::from_u32(..).unwrap_or('\0')`.
        "Char.ofNat" if args.len() == 1 => {
            let n = env.get_arg_u64(&args[0])?;
            let c = char::from_u32(n as u32).unwrap_or('\0');
            Some(IRExpr::Lit(IRLiteral::UInt32(c as u32)))
        }
        // `Char.toNat`/`Char.val : Char → Nat`. Mirrors `reduce_char_to_nat`:
        // the code point as a `Nat` (materialized `UInt64`, like `String.length`).
        "Char.toNat" | "Char.val" if args.len() == 1 => {
            let c = arg_char(env, &args[0])?;
            Some(IRExpr::Lit(IRLiteral::UInt64(u64::from(c as u32))))
        }
        // `Char.isAlpha : Char → Bool`. Mirrors `reduce_char_is_alpha`
        // (`is_alphabetic`).
        "Char.isAlpha" if args.len() == 1 => Some(IRExpr::Lit(IRLiteral::Bool(
            arg_char(env, &args[0])?.is_alphabetic(),
        ))),
        // `Char.isDigit : Char → Bool`. Mirrors `reduce_char_is_digit`, which is
        // ASCII-ONLY (`'0'..='9'`), NOT Unicode `Nd` — match `is_ascii_digit`.
        "Char.isDigit" if args.len() == 1 => Some(IRExpr::Lit(IRLiteral::Bool(
            arg_char(env, &args[0])?.is_ascii_digit(),
        ))),
        // `Char.isWhitespace : Char → Bool`. Mirrors `reduce_char_is_whitespace`
        // (`is_whitespace`).
        "Char.isWhitespace" if args.len() == 1 => Some(IRExpr::Lit(IRLiteral::Bool(
            arg_char(env, &args[0])?.is_whitespace(),
        ))),
        // `Char.isLower : Char → Bool`. Mirrors `reduce_char_is_lower`
        // (`is_lowercase`).
        "Char.isLower" if args.len() == 1 => Some(IRExpr::Lit(IRLiteral::Bool(
            arg_char(env, &args[0])?.is_lowercase(),
        ))),
        // `Char.isUpper : Char → Bool`. Mirrors `reduce_char_is_upper`
        // (`is_uppercase`).
        "Char.isUpper" if args.len() == 1 => Some(IRExpr::Lit(IRLiteral::Bool(
            arg_char(env, &args[0])?.is_uppercase(),
        ))),
        // `Char.toLower : Char → Char`. Mirrors `reduce_char_to_lower` exactly:
        // ASCII fast-path, else the first char of the full Unicode lowercasing
        // (falling back to the original char if that mapping is empty).
        "Char.toLower" if args.len() == 1 => {
            let c = arg_char(env, &args[0])?;
            let lower = if c.is_ascii() {
                c.to_ascii_lowercase()
            } else {
                c.to_lowercase().next().unwrap_or(c)
            };
            Some(IRExpr::Lit(IRLiteral::UInt32(lower as u32)))
        }
        // `Char.toUpper : Char → Char`. Mirrors `reduce_char_to_upper` exactly:
        // ASCII fast-path, else the first char of the full Unicode uppercasing.
        "Char.toUpper" if args.len() == 1 => {
            let c = arg_char(env, &args[0])?;
            let upper = if c.is_ascii() {
                c.to_ascii_uppercase()
            } else {
                c.to_uppercase().next().unwrap_or(c)
            };
            Some(IRExpr::Lit(IRLiteral::UInt32(upper as u32)))
        }
        _ => None,
    }
}

/// Fold an `Array` accessor applied to a statically-known array literal.
///
/// Mirrors [`fold_string`]: the array's elements are tracked via
/// [`KnownVal2::Array`] (recorded from an `Array.mk` constructor), and we fold
/// the size/get/set accessors against that known shape. All cases are total —
/// out-of-bounds `get`/`set` decline to fold (return `None`) rather than guess
/// the runtime's panic/default behaviour, so the call site is left untouched.
///
/// * `Array.size` / `Array.length`: yields the element count as `UInt64`.
/// * `Array.get` / `Array.getD` ... declines unless the index is a known
///   in-range constant, in which case it rebuilds the element as a `Ctor`/`Proj`
///   referencing the original element argument.
/// * `Array.set`: with a known in-range constant index, yields a fresh
///   `Array.mk` constructor with that element replaced.
pub(crate) fn fold_array(op: &str, args: &[IRArg], env: &PropagationEnv) -> Option<IRExpr> {
    match op {
        // `Array.size`/`Array.length`: total, folds to the element count.
        "Array.size" | "Array.length" if args.len() == 1 => {
            let (_, elems) = env.get_arg_array(&args[0])?;
            Some(IRExpr::Lit(IRLiteral::UInt64(elems.len() as u64)))
        }
        // `Array.get arr i`: fold only when the index is a known in-range
        // constant; the selected element argument is rematerialized.
        "Array.get" | "Array.get!" if args.len() == 2 => {
            let (_, elems) = env.get_arg_array(&args[0])?;
            let idx = usize::try_from(env.get_arg_u64(&args[1])?).ok()?;
            let elem = elems.get(idx)?;
            rematerialize_arg(elem, env)
        }
        // `Array.set arr i v`: fold to a fresh `Array.mk` with element `i`
        // replaced by `v`, only when `i` is a known in-range constant.
        "Array.set" | "Array.set!" if args.len() == 3 => {
            let (info, elems) = env.get_arg_array(&args[0])?;
            let idx = usize::try_from(env.get_arg_u64(&args[1])?).ok()?;
            if idx >= elems.len() {
                return None;
            }
            let mut new_elems = elems.to_vec();
            new_elems[idx] = args[2].clone();
            Some(IRExpr::Ctor {
                info: info.clone(),
                args: new_elems,
            })
        }
        _ => None,
    }
}

/// Resolve a statically-known `List` cons-spine to its element arguments in
/// order, or `None` if the spine is not fully ground.
///
/// Walks the linked spine starting at `arg`: at each step the argument must
/// resolve (via [`PropagationEnv::get_arg_list`]) to a tracked `List.nil`
/// (terminates the walk) or `List.cons` node (appends its head and continues
/// with its tail). A tail that resolves to neither — an unbound variable, a
/// symbolic value, or a non-`List` known value — makes the spine non-ground and
/// returns `None` (DECLINE). `max_len` bounds the walk to guard against an
/// unexpectedly long or (defensively) cyclic spine; exceeding it also declines.
fn resolve_list_spine(arg: &IRArg, env: &PropagationEnv, max_len: usize) -> Option<Vec<IRArg>> {
    let mut elems = Vec::new();
    let mut current = arg.clone();
    loop {
        let (_, head, tail) = env.get_arg_list(&current)?;
        match (head, tail) {
            // `List.nil`: end of the spine.
            (None, None) => return Some(elems),
            // `List.cons head tail`: record the head, continue down the tail.
            (Some(head), Some(tail)) => {
                if elems.len() >= max_len {
                    return None;
                }
                elems.push(head.clone());
                current = tail.clone();
            }
            // A malformed node (recorded with exactly one of head/tail) is never
            // produced by `record_expr`; decline defensively rather than guess.
            _ => return None,
        }
    }
}

/// Fold a `List` accessor applied to a statically-known cons-spine.
///
/// Mirrors [`fold_array`]: the spine is tracked as linked [`KnownVal2::List`]
/// nodes (recorded from `List.nil`/`List.cons` constructors) and resolved via
/// [`resolve_list_spine`]. Every arm is observationally equivalent to the
/// kernel's native `List` reducers (`clean-kernel/src/env/native_reducers_init.rs`)
/// or DECLINES (`None`) — a non-ground spine, an out-of-shape op, or a result
/// that cannot be reproduced exactly leaves the call untouched. The list
/// argument is the last argument in the (type-erased) IR spine, matching how
/// `fold_array` reads `Array.size`'s single argument.
///
/// CORRECTNESS — single-expression results only. A `List` in the L5IR is a chain
/// of let-bound `List.cons`/`List.nil` constructors, NOT a flat literal like an
/// `Array.mk`. A const-fold helper can only replace a call with a single
/// [`IRExpr`]; it cannot synthesize the fresh let-bindings a rebuilt cons-spine
/// would require. So list-PRODUCING ops (`append`/`reverse`/`map`/...) are
/// deliberately NOT folded here — emitting them as one nested expression would
/// put an `IRExpr` where the constructor demands an `IRArg::Var` tail, which the
/// IR cannot represent. Only the scalar/element observations below — whose exact
/// kernel value IS a single expression — are folded.
///
/// * `List.length`: the kernel's `reduce_list_length` counts the cons spine; we
///   yield the resolved element count as `UInt64`.
/// * `List.isEmpty`: `[] = true`, `_ :: _ = false` (kernel `List.isEmpty`).
/// * `List.getLast!`: mirrors `reduce_list_get_last_bang` /
///   `get_concrete_list_last` — the last element of a NON-EMPTY spine,
///   rematerialized exactly. The empty case is the kernel's `panic`-backed
///   default, which we do NOT reproduce, so we DECLINE on an empty list.
pub(crate) fn fold_list(
    op: &str,
    args: &[IRArg],
    env: &PropagationEnv,
    max_len: usize,
) -> Option<IRExpr> {
    match op {
        // `List.length : {α} → List α → Nat` — total, folds to the element count.
        // Mirrors `reduce_list_length` / `get_concrete_list_len`.
        "List.length" if args.len() == 1 => {
            let elems = resolve_list_spine(&args[0], env, max_len)?;
            Some(IRExpr::Lit(IRLiteral::UInt64(elems.len() as u64)))
        }
        // `List.isEmpty : {α} → List α → Bool` — `[] = true`, `_ :: _ = false`.
        "List.isEmpty" if args.len() == 1 => {
            let elems = resolve_list_spine(&args[0], env, max_len)?;
            Some(IRExpr::Lit(IRLiteral::Bool(elems.is_empty())))
        }
        // `List.getLast! : {α} → [Inhabited α] → List α → α` — the last element of
        // a non-empty spine. Mirrors `reduce_list_get_last_bang` /
        // `get_concrete_list_last`. The (type-erased) IR call carries just the
        // list, so we read the single argument. On the EMPTY list the kernel
        // reducer returns `None` (leaving Lean's `panic`-backed default to run),
        // which we cannot reproduce as a fold — so we DECLINE there too, and we
        // DECLINE if the last element is not a statically-known value we can
        // rematerialize exactly.
        "List.getLast!" if args.len() == 1 => {
            let elems = resolve_list_spine(&args[0], env, max_len)?;
            let last = elems.last()?;
            rematerialize_arg(last, env)
        }
        _ => None,
    }
}

/// Rebuild an `IRExpr` for a known element argument, used by `Array.get`
/// folding. A concrete known value becomes its literal/string/ctor form; an
/// element whose value is not statically known declines to fold.
fn rematerialize_arg(arg: &IRArg, env: &PropagationEnv) -> Option<IRExpr> {
    let IRArg::Var(v) = arg else {
        return None;
    };
    match env.get(*v)? {
        KnownVal2::Lit(l) => Some(IRExpr::Lit(l.clone())),
        KnownVal2::Str(s) => Some(IRExpr::String(s.clone())),
        KnownVal2::Bool(b) => Some(IRExpr::Lit(IRLiteral::Bool(*b))),
        KnownVal2::Ctor { info, args, .. } => Some(IRExpr::Ctor {
            info: info.clone(),
            args: args.clone(),
        }),
        KnownVal2::Array { info, elems } => Some(IRExpr::Ctor {
            info: info.clone(),
            args: elems.clone(),
        }),
        // A `List` spine node tracks only head/tail (with the type parameter
        // erased); rebuilding its exact original constructor argument layout
        // here is not guaranteed faithful, so DECLINE rather than guess.
        KnownVal2::List { .. } => None,
    }
}

pub(crate) fn fold_cmp(op: &str, lhs: u64, rhs: u64) -> Option<bool> {
    match op {
        "Nat.beq" | "UInt64.beq" => Some(lhs == rhs),
        "Nat.ble" | "UInt64.ble" => Some(lhs <= rhs),
        "Nat.blt" | "UInt64.blt" => Some(lhs < rhs),
        "Nat.bge" => Some(lhs >= rhs),
        "Nat.bgt" => Some(lhs > rhs),
        "Int.beq" => Some((lhs as i64) == (rhs as i64)),
        "Int.ble" => Some((lhs as i64) <= (rhs as i64)),
        "Int.blt" => Some((lhs as i64) < (rhs as i64)),
        "Int.bge" => Some((lhs as i64) >= (rhs as i64)),
        "Int.bgt" => Some((lhs as i64) > (rhs as i64)),
        _ => None,
    }
}

/// Fixed-width integer literal kind, carrying the bit width and a re-wrap
/// constructor so bitwise/shift folds preserve the operand's exact type.
///
/// We deliberately keep this distinct from `extract_u64` (which lossily widens
/// every integer to `u64` and re-tags the result as `UInt64`). Bitwise and
/// shift results depend on the operand width — e.g. `UInt8.complement 0` is
/// `255`, not `u64::MAX` — so we must compute *and re-tag* at the original
/// width to match the runtime (`native_eval::eval_int_binop`).
struct IntWidth {
    /// Bit width of the type (`8`, `16`, `32`, or `64`).
    bits: u32,
    /// Value already reduced into the type's range.
    value: u64,
    /// Re-wrap a width-reduced value back into the original literal variant.
    rewrap: fn(u64) -> IRLiteral,
}

/// Classify a fixed-width unsigned integer literal. Returns `None` for `Nat`
/// (unbounded) and non-integer literals — bitwise folds over those are handled
/// separately or left untouched (conservative).
fn classify_uint(lit: &IRLiteral) -> Option<IntWidth> {
    match lit {
        IRLiteral::UInt8(v) => Some(IntWidth {
            bits: 8,
            value: u64::from(*v),
            rewrap: |x| IRLiteral::UInt8(x as u8),
        }),
        IRLiteral::UInt16(v) => Some(IntWidth {
            bits: 16,
            value: u64::from(*v),
            rewrap: |x| IRLiteral::UInt16(x as u16),
        }),
        IRLiteral::UInt32(v) => Some(IntWidth {
            bits: 32,
            value: u64::from(*v),
            rewrap: |x| IRLiteral::UInt32(x as u32),
        }),
        IRLiteral::UInt64(v) => Some(IntWidth {
            bits: 64,
            value: *v,
            rewrap: IRLiteral::UInt64,
        }),
        IRLiteral::USize(v) => Some(IntWidth {
            bits: 64,
            value: *v as u64,
            rewrap: |x| IRLiteral::USize(x as usize),
        }),
        _ => None,
    }
}

/// Width mask: `2^bits - 1` for `bits < 64`, else all ones. Used to keep
/// results inside the operand's range, exactly mirroring the runtime's
/// `NativeType::modulus` reduction.
fn width_mask(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// Strip a recognized fixed-width unsigned-integer prefix from `op`, returning
/// the bare operation suffix. Recognizing the prefix here keeps the bitwise
/// fold from ever mistaking a same-named operation on an unrelated type.
fn strip_uint_prefix(op: &str) -> Option<&str> {
    op.strip_prefix("UInt8.")
        .or_else(|| op.strip_prefix("UInt16."))
        .or_else(|| op.strip_prefix("UInt32."))
        .or_else(|| op.strip_prefix("UInt64."))
        .or_else(|| op.strip_prefix("USize."))
}

/// Fold a fixed-width unsigned-integer bitwise or shift operation.
///
/// Binary ops (`land`/`lor`/`xor`/`shiftLeft`/`shiftRight`) take two operands
/// of the *same* width; the unary `complement` takes one. Results are computed
/// at the operand width and re-tagged with the original literal variant. The
/// semantics match `native_eval::eval_int_binop` / `eval_unaryop` exactly:
///
/// * `land`/`lor`/`xor`: bitwise, masked to width.
/// * `shiftLeft`/`shiftRight`: if the shift amount is `>= bit_width` the result
///   is `0` (matching the runtime's saturating guard, and avoiding Rust's
///   shift-overflow panic); otherwise shift then mask.
/// * `complement`: `(!v)` masked to width.
///
/// Returns `None` for any unrecognized op, mismatched widths, or non-fixed-width
/// operands — leaving the call site untouched (conservative).
pub(crate) fn fold_bitwise(op: &str, args: &[IRLiteral]) -> Option<IRLiteral> {
    let suffix = strip_uint_prefix(op)?;
    match suffix {
        "land" | "lor" | "xor" | "lxor" | "shiftLeft" | "shiftRight" if args.len() == 2 => {
            let lhs = classify_uint(&args[0])?;
            let rhs = classify_uint(&args[1])?;
            // Both operands must share the same width: a cross-width bitwise op
            // is not a meaningful fixed-width operation, so refuse to fold.
            if lhs.bits != rhs.bits {
                return None;
            }
            let mask = width_mask(lhs.bits);
            let (a, b) = (lhs.value, rhs.value);
            let result = match suffix {
                "land" => a & b,
                "lor" => a | b,
                "xor" | "lxor" => a ^ b,
                "shiftLeft" => {
                    if b >= u64::from(lhs.bits) {
                        0
                    } else {
                        a.wrapping_shl(b as u32)
                    }
                }
                "shiftRight" => {
                    if b >= u64::from(lhs.bits) {
                        0
                    } else {
                        a >> b
                    }
                }
                _ => return None,
            };
            Some((lhs.rewrap)(result & mask))
        }
        "complement" if args.len() == 1 => {
            let w = classify_uint(&args[0])?;
            let mask = width_mask(w.bits);
            Some((w.rewrap)((!w.value) & mask))
        }
        _ => None,
    }
}

/// Fold a `Float` arithmetic operation on two same-typed float literals.
///
/// The runtime (`native_eval::eval_float_binop`) computes these with native
/// IEEE 754 operations: division/modulus by zero yields `Inf`/`NaN` rather than
/// trapping, so every case is *total* and safe to fold. We preserve the operand
/// subtype: `Float32` operands fold with `f32` arithmetic, `Float64` with `f64`.
/// Mixed float widths return `None` (no fold).
///
/// Lean op names for the `Float` type are unprefixed-by-width (`Float.add`,
/// `Float.div`, ...); the runtime treats `Float` as a 64-bit double. We accept
/// the same `Float.` names and additionally fold `Float32`-tagged literals at
/// `f32` precision so an IR that distinguishes the two stays faithful.
pub(crate) fn fold_float(op: &str, args: &[IRLiteral]) -> Option<IRLiteral> {
    let suffix = op.strip_prefix("Float.")?;
    if args.len() != 2 {
        return None;
    }
    match (&args[0], &args[1]) {
        (IRLiteral::Float64(a), IRLiteral::Float64(b)) => {
            float64_binop(suffix, *a, *b).map(IRLiteral::Float64)
        }
        (IRLiteral::Float32(a), IRLiteral::Float32(b)) => {
            float32_binop(suffix, *a, *b).map(IRLiteral::Float32)
        }
        _ => None,
    }
}

fn float64_binop(suffix: &str, a: f64, b: f64) -> Option<f64> {
    match suffix {
        "add" => Some(a + b),
        "sub" => Some(a - b),
        "mul" => Some(a * b),
        // IEEE 754: division/modulus by zero is defined (Inf/NaN), not a trap.
        "div" => Some(a / b),
        "mod" => Some(a % b),
        _ => None,
    }
}

fn float32_binop(suffix: &str, a: f32, b: f32) -> Option<f32> {
    match suffix {
        "add" => Some(a + b),
        "sub" => Some(a - b),
        "mul" => Some(a * b),
        "div" => Some(a / b),
        "mod" => Some(a % b),
        _ => None,
    }
}

fn is_pure_function(name: &str) -> bool {
    name.starts_with("Nat.")
        || name.starts_with("Int.")
        || name.starts_with("Bool.")
        || name.starts_with("String.")
        || name.starts_with("Array.")
        || name.starts_with("List.")
        || name.starts_with("Char.")
        || name.starts_with("UInt8.")
        || name.starts_with("UInt16.")
        || name.starts_with("UInt32.")
        || name.starts_with("UInt64.")
        || name.starts_with("USize.")
        || name.starts_with("Float.")
}

/// Partial evaluation of a pure, total function applied to all-constant
/// arguments. Dispatches to the typed fold helpers by operation kind and
/// returns the folded constant IR expression, or `None` when the function is
/// not a recognized pure/total operation (conservative: leaves the call site
/// untouched). All callees here are referentially transparent and total — no
/// effects, no partiality beyond the guards already encoded in the helpers
/// (e.g. `Nat.div` by zero yields `None`), so substituting the result for the
/// call preserves observable semantics.
fn eval_pure_apply(
    name: &str,
    args: &[IRArg],
    env: &PropagationEnv,
    max_string_length: usize,
    max_list_length: usize,
) -> Option<IRExpr> {
    // Arithmetic: binary Nat/Int operations.
    if args.len() == 2 {
        if let (Some(l), Some(r)) = (env.get_arg_u64(&args[0]), env.get_arg_u64(&args[1])) {
            if let Some(v) = fold_arith(name, l, r) {
                return Some(IRExpr::Lit(IRLiteral::UInt64(v)));
            }
            if let Some(v) = fold_cmp(name, l, r) {
                return Some(IRExpr::Lit(IRLiteral::Bool(v)));
            }
        }
    }
    // Unary `Int.abs`.
    if args.len() == 1 {
        if let Some(v) = env
            .get_arg_u64(&args[0])
            .and_then(|x| fold_int_abs(name, x))
        {
            return Some(IRExpr::Lit(IRLiteral::UInt64(v)));
        }
    }
    // Boolean connectives.
    if let Some(v) = fold_bool(name, args, env) {
        return Some(IRExpr::Lit(IRLiteral::Bool(v)));
    }
    // String operations (length-guarded against `max_string_length`).
    if let Some(v) = fold_string(name, args, env, max_string_length) {
        return Some(v);
    }
    // Array accessors over a statically-known `Array.mk` literal.
    if let Some(v) = fold_array(name, args, env) {
        return Some(v);
    }
    // List accessors over a statically-known `List.nil`/`List.cons` spine.
    if let Some(v) = fold_list(name, args, env, max_list_length) {
        return Some(v);
    }
    // `Char.*` operations over a statically-known `Char` (UInt32 code point).
    if let Some(v) = fold_char(name, args, env) {
        return Some(v);
    }
    // Fixed-width bitwise/shift and Float arithmetic operate on the *typed*
    // literals (width/subtype must be preserved), so resolve the args to their
    // exact `IRLiteral`s. `None` from any arg => not all-constant => no fold.
    if let Some(lits) = collect_arg_lits(args, env) {
        if let Some(v) = fold_bitwise(name, &lits) {
            return Some(IRExpr::Lit(v));
        }
        if let Some(v) = fold_float(name, &lits) {
            return Some(IRExpr::Lit(v));
        }
    }
    None
}

/// Resolve every argument to its known typed literal, or `None` if any argument
/// is not a known literal (e.g. `Erased`, a ctor, or an unbound variable).
fn collect_arg_lits(args: &[IRArg], env: &PropagationEnv) -> Option<Vec<IRLiteral>> {
    args.iter().map(|a| env.get_arg_lit(a).cloned()).collect()
}

// -- Folding engine ----------------------------------------------------------

fn try_fold_apply(
    fn_id: &FnId,
    args: &[IRArg],
    env: &PropagationEnv,
    config: &ConstFoldExt2Config,
    stats: &mut ConstFoldExt2Stats,
) -> Option<IRExpr> {
    let name = fn_id.0.to_string();
    if config.fold_arithmetic && args.len() == 2 {
        if let (Some(l), Some(r)) = (env.get_arg_u64(&args[0]), env.get_arg_u64(&args[1])) {
            if let Some(v) = fold_arith(&name, l, r) {
                stats.arithmetic_folds += 1;
                return Some(IRExpr::Lit(IRLiteral::UInt64(v)));
            }
        }
    }
    if config.fold_arithmetic && args.len() == 1 {
        if let Some(v) = env
            .get_arg_u64(&args[0])
            .and_then(|x| fold_int_abs(&name, x))
        {
            stats.arithmetic_folds += 1;
            return Some(IRExpr::Lit(IRLiteral::UInt64(v)));
        }
    }
    if config.fold_boolean {
        if let Some(v) = fold_bool(&name, args, env) {
            stats.boolean_folds += 1;
            return Some(IRExpr::Lit(IRLiteral::Bool(v)));
        }
    }
    if config.fold_string {
        if let Some(v) = fold_string(&name, args, env, config.max_string_length) {
            stats.string_folds += 1;
            return Some(v);
        }
    }
    if config.fold_array {
        if let Some(v) = fold_array(&name, args, env) {
            stats.array_folds += 1;
            return Some(v);
        }
    }
    if config.fold_list {
        if let Some(v) = fold_list(&name, args, env, config.max_list_length) {
            stats.list_folds += 1;
            return Some(v);
        }
    }
    if config.fold_char {
        if let Some(v) = fold_char(&name, args, env) {
            stats.char_folds += 1;
            return Some(v);
        }
    }
    if config.fold_comparisons && args.len() == 2 {
        if let (Some(l), Some(r)) = (env.get_arg_u64(&args[0]), env.get_arg_u64(&args[1])) {
            if let Some(v) = fold_cmp(&name, l, r) {
                stats.comparison_folds += 1;
                return Some(IRExpr::Lit(IRLiteral::Bool(v)));
            }
        }
    }
    if config.fold_bitwise || config.fold_float {
        // Both bitwise/shift and Float arithmetic need the *typed* literals
        // (width/subtype is load-bearing for re-tagging), so collect them once.
        if let Some(lits) = collect_arg_lits(args, env) {
            if config.fold_bitwise {
                if let Some(v) = fold_bitwise(&name, &lits) {
                    stats.bitwise_folds += 1;
                    return Some(IRExpr::Lit(v));
                }
            }
            if config.fold_float {
                if let Some(v) = fold_float(&name, &lits) {
                    stats.float_folds += 1;
                    return Some(IRExpr::Lit(v));
                }
            }
        }
    }
    if config.fold_partial_eval && is_pure_function(&name) {
        // A non-empty argument list whose entries are all compile-time-known
        // constants. `Erased` args never carry a value, so they are excluded.
        let all_known = !args.is_empty()
            && args
                .iter()
                .all(|a| matches!(a, IRArg::Var(v) if env.get(*v).is_some()));
        if all_known {
            // Partial evaluation: actually compute the result of the pure
            // function on its constant arguments and replace the call with the
            // folded constant. Returns `None` for any function we do not
            // recognize as pure-and-total, leaving the call site untouched.
            if let Some(folded) = eval_pure_apply(
                &name,
                args,
                env,
                config.max_string_length,
                config.max_list_length,
            ) {
                stats.partial_eval_folds += 1;
                return Some(folded);
            }
        }
    }
    None
}

fn fold_expr(
    expr: &IRExpr,
    env: &PropagationEnv,
    config: &ConstFoldExt2Config,
    stats: &mut ConstFoldExt2Stats,
) -> IRExpr {
    match expr {
        IRExpr::Apply { fn_id, args } => {
            try_fold_apply(fn_id, args, env, config, stats).unwrap_or_else(|| expr.clone())
        }
        IRExpr::Tag(IRArg::Var(v)) if config.fold_ctor_tag => {
            if let Some(tag) = env.get_tag(*v) {
                stats.ctor_tag_folds += 1;
                return IRExpr::Lit(IRLiteral::UInt64(tag as u64));
            }
            expr.clone()
        }
        IRExpr::Proj {
            idx,
            arg: IRArg::Var(v),
            ty,
        } if config.fold_projection => {
            if let Some(field_arg) = env.get_ctor_arg(*v, *idx) {
                stats.projection_folds += 1;
                if let IRArg::Var(fv) = field_arg {
                    if let Some(known) = env.get(*fv) {
                        // A `List` spine node cannot be rebuilt as a single
                        // faithful constructor (its type arg is erased and its
                        // tail is a separate spine var), so it falls through to
                        // the safe `Proj` over the field argument below.
                        match known {
                            KnownVal2::Lit(l) => return IRExpr::Lit(l.clone()),
                            KnownVal2::Str(s) => return IRExpr::String(s.clone()),
                            KnownVal2::Bool(b) => return IRExpr::Lit(IRLiteral::Bool(*b)),
                            KnownVal2::Ctor { info, args, .. }
                            | KnownVal2::Array { info, elems: args } => {
                                return IRExpr::Ctor {
                                    info: info.clone(),
                                    args: args.clone(),
                                }
                            }
                            KnownVal2::List { .. } => {}
                        }
                    }
                }
                return IRExpr::Proj {
                    idx: *idx,
                    ty: ty.clone(),
                    arg: field_arg.clone(),
                };
            }
            expr.clone()
        }
        _ => expr.clone(),
    }
}

/// Fold rest continuation for pass-through body nodes.
fn fold_rest(
    rest: &IRBody,
    env: &mut PropagationEnv,
    cfg: &ConstFoldExt2Config,
    s: &mut ConstFoldExt2Stats,
) -> Box<IRBody> {
    Box::new(fold_body(rest, env, cfg, s))
}

fn fold_body(
    body: &IRBody,
    env: &mut PropagationEnv,
    config: &ConstFoldExt2Config,
    stats: &mut ConstFoldExt2Stats,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let new_value = fold_expr(value, env, config, stats);
            if config.propagate_constants {
                env.record_expr(*var, &new_value);
                stats.propagations += 1;
            }
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: new_value,
                rest: fold_rest(rest, env, config, stats),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let mut jp_env = env.clone_scope();
            IRBody::JDecl {
                jp: *jp,
                params: params.clone(),
                body: Box::new(fold_body(jp_body, &mut jp_env, config, stats)),
                rest: fold_rest(rest, env, config, stats),
            }
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            if config.fold_dead_branches {
                let tag = env
                    .get_tag(*scrutinee)
                    .or_else(|| match env.get(*scrutinee)? {
                        KnownVal2::Bool(b) => Some(u32::from(*b)),
                        _ => None,
                    });
                if let Some(t) = tag {
                    for alt in alts {
                        if alt.ctor.tag == t {
                            stats.dead_branch_folds += 1;
                            return fold_body(&alt.body, &mut env.clone_scope(), config, stats);
                        }
                    }
                }
            }
            let new_alts = alts
                .iter()
                .map(|alt| IRAlt {
                    ctor: alt.ctor.clone(),
                    body: Box::new(fold_body(&alt.body, &mut env.clone_scope(), config, stats)),
                })
                .collect();
            let new_def = default
                .as_ref()
                .map(|d| Box::new(fold_body(d, &mut env.clone_scope(), config, stats)));
            IRBody::Case {
                scrutinee: *scrutinee,
                alts: new_alts,
                default: new_def,
            }
        }
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: fold_rest(rest, env, config, stats),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: fold_rest(rest, env, config, stats),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: *var,
            idx: *idx,
            value: *value,
            rest: fold_rest(rest, env, config, stats),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: fold_rest(rest, env, config, stats),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: *var,
            idx: *idx,
            value: *value,
            rest: fold_rest(rest, env, config, stats),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: *var,
            n: *n,
            offset: *offset,
            value: *value,
            ty: ty.clone(),
            rest: fold_rest(rest, env, config, stats),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        IRBody::Ret(arg) => IRBody::Ret(arg.clone()),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

// -- Top-level entry points --------------------------------------------------

pub(crate) fn fold_constants_ext2(
    decls: &mut [IRDecl],
    config: &ConstFoldExt2Config,
) -> ConstFoldExt2Stats {
    let mut total = ConstFoldExt2Stats::default();
    for iteration in 0..config.max_iterations {
        let mut iter_stats = ConstFoldExt2Stats::default();
        let mut changed = false;
        for decl in decls.iter_mut() {
            let mut env = PropagationEnv::new();
            let old_body = decl.body.clone();
            let new_body = fold_body(&old_body, &mut env, config, &mut iter_stats);
            if new_body != old_body {
                changed = true;
            }
            decl.body = new_body;
        }
        total.merge(&iter_stats);
        total.iterations = iteration + 1;
        if !changed {
            break;
        }
    }
    total
}

pub(crate) fn fold_constants_ext2_default(decls: &mut [IRDecl]) -> ConstFoldExt2Stats {
    fold_constants_ext2(decls, &ConstFoldExt2Config::default())
}

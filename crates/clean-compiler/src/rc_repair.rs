// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Representation-aware reference counting on the FINAL (post-boxing) L5IR
//! (WS6.2).
//!
//! # The hole
//!
//! RC insertion (`rc::insert`) runs on LCNF, BEFORE `to_ir` and explicit
//! boxing. It decides per LCNF type, and a source-scalar type (`UInt64`,
//! `Bool`, `Char`, …; `rc::insert::is_scalar_type`) never needs RC — so the
//! LCNF pass inserts nothing for such a variable. But the final
//! representation is decided later: `to_ir` types the result of a call to a
//! boxed callee (`HAdd.hAdd`, `HMul.hMul`, a closure) as an OBJECT, and
//! boxing introduces fresh `Box` temporaries. For
//! `def sqLet (a : UInt64) : UInt64 := let t := a + 1; t * t` the boxed IR
//! passes the one owned object `t` TWICE to `l_HMul_hMul`, which consumes
//! both through `clean_apply_2` — with no `inc`: a double release, SIGBUS at
//! run time, through both the C and the trust-ir back ends. The result of
//! the multiplication, unboxed and never released, leaked on the same path.
//! Boxing already knew LCNF RC is not representation-aware in the
//! object→scalar direction (it drops `Inc`/`Dec` on variables that became
//! scalar); nothing covered the scalar→object direction.
//!
//! # The rule
//!
//! Two parts, both on the boxed IR:
//!
//! * [`rc_repair_boxed`] manages ONLY the variables LCNF RC did not: object
//!   variables whose LCNF type is scalar (recorded by `to_ir` in
//!   [`crate::to_ir::ToIROutput::rc_unmanaged`]) and every object variable
//!   boxing itself introduced (a `Box` temporary, an expensive-constant call,
//!   every variable of a boxing-generated wrapper). For those it runs the
//!   Counting-Immutable-Beans insertion on the final IR: an `inc` before every
//!   owned consumption the variable survives, a `dec` at the death point of a
//!   variable that is not consumed, and a `dec` at the head of every branch
//!   the variable is dead in. A deficit on any OTHER variable is never
//!   repaired: it is a genuine LCNF RC defect.
//!   The object→scalar direction is repaired here too
//!   (`release_consuming_unboxes`): where boxing replaced a consuming use of
//!   an LCNF-managed object (`ret v`, an owned call argument, a jump
//!   argument) by `u := unbox v`, the object is released right after the
//!   unbox — the consumption the representation change took away.
//! * [`verify_rc_linearity`] then checks EVERY object variable of every
//!   declaration (see `rc_repair_linearity.rs` for the exact rule) and fails the build
//!   with `RC linearity violation in {decl}: object %{v} is consumed {n}
//!   times with {k} incs on path {p}: …` on the first path that is not
//!   linear. It runs on every build, not only debug ones. It is the
//!   structural RC check the backend TV certificate explicitly does not
//!   provide (`emit_trust_ir_tv`: "RC insertion … remain[s] exactly as
//!   unverified as before"), and it turns a regression of the repair into a
//!   compile error instead of a crash.
//!
//! # What the verifier found
//!
//! Run over the 1002 computable prelude roots, the total verifier refused
//! 118 that the repair's domain does not cover. Each was a real release the
//! pipeline never emitted, fixed where it was lost rather than waived:
//!
//! * boxing's object→scalar cast at a consuming position (above) — 62 roots;
//! * `rc::insert` never released a non-param local that is live into a
//!   `cases` but dead in a branch (the scrutinee included), nor a structure
//!   whose last use is a projection — Lean's `ExplicitRC` rules for `case`
//!   and `proj` (`rc::insert::insert_rc_cases`, `helpers::process_let_value`);
//! * `to_ir`'s scalar decode / alias rewrites (`UIntN.ofNat`, `Char.mk`,
//!   `BitVec.ofFin`) replaced a consuming call by a read without releasing
//!   the operands the call consumed (`to_ir::pseudo_ops`).
//!
//! After the fixes all 1002 roots pass at `-O0`, `-O1` and `-O2`.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;

use clean_kernel::Name;

use crate::error::CompilerError;
use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use crate::rc::borrow::{BorrowMap, Ownership};

#[path = "rc_repair_linearity.rs"]
pub(crate) mod linearity;

/// A path on which an object variable is not linear.
///
/// Rendered as `RC linearity violation in {decl}: object %{var} is consumed
/// {consumed} times with {incs} incs on path {path}: {detail}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RcLinearityViolation {
    /// Declaration whose body is not linear.
    pub(crate) decl: String,
    /// The offending variable (`VarId`).
    pub(crate) var: u32,
    /// Owned consumptions of the variable on the path, up to the violation.
    pub(crate) consumed: u32,
    /// `Inc` units applied to the variable on the path, up to the violation.
    pub(crate) incs: u32,
    /// The path: `entry`, then `/alt<tag>`, `/default` and `/jp<id>` steps.
    pub(crate) path: String,
    /// What went wrong.
    pub(crate) detail: String,
}

impl fmt::Display for RcLinearityViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "RC linearity violation in {}: object %{} is consumed {} times with {} incs on path {}: {}",
            self.decl, self.var, self.consumed, self.incs, self.path, self.detail
        )
    }
}

impl std::error::Error for RcLinearityViolation {}

/// Per-declaration set of IR variables whose LCNF type is a source scalar
/// (so LCNF RC inserted no `inc`/`dec` for them), as recorded by `to_ir`.
pub(crate) type RcUnmanagedVars = HashMap<Name, HashSet<VarId>>;

/// Whether the post-boxing RC repair runs. `Disabled` exists for the
/// mutation control only: with the repair off, [`verify_rc_linearity`] must
/// REFUSE the programs the repair fixes — never a looser build.
///
/// `Disabled` exists only in test builds: production code cannot switch the
/// repair off at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RcRepairMode {
    /// Run [`rc_repair_boxed`] (the production setting).
    Enabled,
    /// Skip it; the verifier still runs and refuses what is not linear.
    #[cfg(test)]
    Disabled,
}

/// Fail-closed check that every object variable of every declaration is
/// linear, under the pipeline's all-owned calling convention
/// (`rc::abi_owned_map`: every parameter of every callee is owned).
pub(crate) fn verify_rc_linearity(decls: &[IRDecl]) -> Result<(), CompilerError> {
    verify_rc_linearity_with_borrows(decls, &BorrowMap::new())
}

/// [`verify_rc_linearity`] under explicit borrow signatures: a declaration
/// listed in `sigs` has the listed parameter ownership (owned past the end
/// of its list, exactly as `rc::insert::insert_rc` reads it), and a call
/// position is owned iff the callee is absent from `sigs` or lists that
/// position as owned (exactly as `rc::insert::helpers` reads it).
pub(crate) fn verify_rc_linearity_with_borrows(
    decls: &[IRDecl],
    sigs: &BorrowMap,
) -> Result<(), CompilerError> {
    for decl in decls {
        linearity::check_decl(decl, sigs).map_err(|v| CompilerError::RcLinearity {
            decl: v.decl,
            var: v.var,
            consumed: v.consumed,
            incs: v.incs,
            path: v.path,
            detail: v.detail,
        })?;
    }
    Ok(())
}

/// Insert the `inc`/`dec` operations LCNF RC could not, on the boxed IR.
///
/// * `ir_decls` — the pre-boxing IR (`to_ir` output), used to tell which
///   variables boxing introduced;
/// * `boxed_ir_decls` — the boxing output, rewritten in place;
/// * `unmanaged` — per declaration, the variables whose LCNF type is scalar.
///
/// The domain of a declaration is its `VDecl`-bound object variables that
/// carry no `Inc`/`Dec` already and that either are LCNF-scalar, or are not
/// bound in the pre-boxing twin (boxing introduced them), or belong to a
/// declaration boxing generated. Nothing outside the domain is touched.
pub(crate) fn rc_repair_boxed(
    ir_decls: &[IRDecl],
    boxed_ir_decls: Vec<IRDecl>,
    unmanaged: &RcUnmanagedVars,
) -> Vec<IRDecl> {
    let pre: HashMap<&Name, &IRDecl> = ir_decls.iter().map(|d| (&d.name, d)).collect();
    let empty = HashSet::new();
    boxed_ir_decls
        .into_iter()
        .map(|decl| {
            let pre_bound = pre.get(&decl.name).map(|d| bound_vars(d));
            let lcnf_scalar = unmanaged.get(&decl.name).unwrap_or(&empty);
            let domain = repair_domain(&decl, pre_bound.as_ref(), lcnf_scalar);
            let decl = release_consuming_unboxes(decl, pre_bound.as_ref(), &domain);
            if domain.is_empty() {
                return decl;
            }
            let mut repair = Repair::new(&decl, domain);
            let (body, _) = repair.body(&decl.body);
            IRDecl { body, ..decl }
        })
        .collect()
}

/// Every variable a declaration binds (params, `VDecl`s, join-point params).
fn bound_vars(decl: &IRDecl) -> HashSet<u32> {
    let mut out: HashSet<u32> = decl.params.iter().map(|(v, _)| v.0).collect();
    let mut stack = vec![&decl.body];
    while let Some(body) = stack.pop() {
        match body {
            IRBody::VDecl { var, rest, .. } => {
                out.insert(var.0);
                stack.push(rest);
            }
            IRBody::JDecl {
                params, body, rest, ..
            } => {
                out.extend(params.iter().map(|(v, _)| v.0));
                stack.push(body);
                stack.push(rest);
            }
            IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => stack.push(rest),
            IRBody::Case { alts, default, .. } => {
                stack.extend(alts.iter().map(|a| a.body.as_ref()));
                if let Some(default) = default {
                    stack.push(default);
                }
            }
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
        }
    }
    out
}

/// The repair domain of one boxed declaration: `VDecl`-bound object
/// variables with no existing `Inc`/`Dec`, that LCNF RC did not manage.
fn repair_domain(
    decl: &IRDecl,
    pre_bound: Option<&HashSet<u32>>,
    lcnf_scalar: &HashSet<VarId>,
) -> BTreeMap<u32, Binding> {
    let mut types: HashMap<u32, IRType> =
        decl.params.iter().map(|(v, t)| (v.0, t.clone())).collect();
    let mut rc_touched: HashSet<u32> = HashSet::new();
    let mut candidates: Vec<(u32, &IRExpr)> = Vec::new();
    let mut stack = vec![&decl.body];
    while let Some(body) = stack.pop() {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                types.insert(var.0, ty.clone());
                if ty.is_object() {
                    candidates.push((var.0, value));
                }
                stack.push(rest);
            }
            IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => {
                rc_touched.insert(var.0);
                stack.push(rest);
            }
            IRBody::JDecl {
                params, body, rest, ..
            } => {
                for (v, t) in params {
                    types.insert(v.0, t.clone());
                }
                stack.push(body);
                stack.push(rest);
            }
            IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => stack.push(rest),
            IRBody::Case { alts, default, .. } => {
                stack.extend(alts.iter().map(|a| a.body.as_ref()));
                if let Some(default) = default {
                    stack.push(default);
                }
            }
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
        }
    }
    let mut domain = BTreeMap::new();
    for (var, value) in candidates {
        if rc_touched.contains(&var) {
            continue;
        }
        let unmanaged = match pre_bound {
            None => true,
            Some(pre) => !pre.contains(&var) || lcnf_scalar.contains(&VarId(var)),
        };
        if !unmanaged {
            continue;
        }
        let binding = match value {
            IRExpr::Proj {
                arg: IRArg::Var(parent),
                ..
            } => match types.get(&parent.0) {
                Some(t) if t.is_object() => Binding::Borrowed,
                Some(t) if t.is_scalar() => Binding::Owned,
                _ => continue,
            },
            IRExpr::Proj {
                arg: IRArg::Erased, ..
            } => continue,
            _ => Binding::Owned,
        };
        domain.insert(var, binding);
    }
    domain
}

/// The object→scalar direction (WS6.2): boxing casts an OBJECT argument to
/// a SCALAR parameter, a scalar join-point parameter or a scalar return with
/// `u := unbox v`. At such a site the pre-boxing IR CONSUMED `v` (an owned
/// call position, a `Jmp` argument, `ret`) and LCNF RC balanced `v` for that
/// consumption — but `unbox` only reads. Unrepaired, every such site leaks
/// one reference (measured: 118 of the 1002 computable prelude roots, e.g.
/// `Bool.xor`'s `ret (unbox (Bool.not b))`). Release it right after the
/// unbox, which is exactly the consumption the representation change took
/// away.
///
/// Only a cast BOXING introduced (the temp is absent from the pre-boxing
/// twin) whose value feeds a consuming position of the instruction it was
/// prefixed to qualifies; a cast feeding a `case` scrutinee (a read in both
/// representations) does not. Domain variables are skipped: the domain
/// repair manages them whole, treating every `unbox` as the read it is.
///
/// The object→erased direction is the same representation change: an
/// object argument of a `Unit`/`PUnit` parameter (bound erased by
/// `to_ir::lower_param`, never read or released by the callee) is cast to
/// an `Erased` temp with `u := box v`. LCNF RC cannot see it: a projection
/// out of a polymorphic field has no instantiated type there (`ForInStep.yield
/// PUnit.unit`'s field is typed `α`), so it is managed and balanced for the
/// call. Measured (X4): `for c in xs do IO.println c` in `IO`, whose loop
/// continuation now calls `go(tail, s)` directly with the projected `PUnit`
/// state, and the non-recursive `f p.1 p.2` for `f : PUnit → Nat → Nat`,
/// were refused with `object %n is consumed 0 times with 1 incs`.
fn release_consuming_unboxes(
    decl: IRDecl,
    pre_bound: Option<&HashSet<u32>>,
    domain: &BTreeMap<u32, Binding>,
) -> IRDecl {
    let Some(pre) = pre_bound else {
        // A boxing-generated declaration has no pre-boxing twin: its casts
        // are its own and its variables are all in the domain.
        return decl;
    };
    let mut types: HashMap<u32, IRType> =
        decl.params.iter().map(|(v, t)| (v.0, t.clone())).collect();
    collect_types(&decl.body, &mut types);
    let ctx = UnboxCtx {
        pre,
        domain,
        types: &types,
    };
    let body = ctx.rewrite(decl.body);
    IRDecl { body, ..decl }
}

fn collect_types(body: &IRBody, types: &mut HashMap<u32, IRType>) {
    let mut stack = vec![body];
    while let Some(body) = stack.pop() {
        match body {
            IRBody::VDecl { var, ty, rest, .. } => {
                types.insert(var.0, ty.clone());
                stack.push(rest);
            }
            IRBody::JDecl {
                params, body, rest, ..
            } => {
                for (v, t) in params {
                    types.insert(v.0, t.clone());
                }
                stack.push(body);
                stack.push(rest);
            }
            IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => stack.push(rest),
            IRBody::Case { alts, default, .. } => {
                stack.extend(alts.iter().map(|a| a.body.as_ref()));
                if let Some(default) = default {
                    stack.push(default);
                }
            }
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
        }
    }
}

struct UnboxCtx<'a> {
    pre: &'a HashSet<u32>,
    domain: &'a BTreeMap<u32, Binding>,
    types: &'a HashMap<u32, IRType>,
}

impl UnboxCtx<'_> {
    fn rewrite(&self, body: IRBody) -> IRBody {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                // An `unbox`, or the cast boxing makes for an object passed
                // to an ERASED slot (a `Unit`/`PUnit` parameter, which
                // `to_ir::lower_param` binds erased: `u : Erased := box v`).
                // Both only read `v`; neither hands its reference on.
                let src = match &value {
                    IRExpr::Unbox {
                        arg: IRArg::Var(src),
                        ..
                    } => Some(*src),
                    IRExpr::Box {
                        arg: IRArg::Var(src),
                        ..
                    } if matches!(ty, IRType::Erased | IRType::Void) => Some(*src),
                    _ => None,
                };
                let release = src.filter(|src| {
                    !self.pre.contains(&var.0)
                        && !self.domain.contains_key(&src.0)
                        && self.types.get(&src.0).is_some_and(IRType::is_object)
                        && feeds_consuming_position(var, &rest)
                });
                let rest = self.rewrite(*rest);
                let rest = match release {
                    Some(src) => IRBody::Dec {
                        var: src,
                        rest: Box::new(rest),
                    },
                    None => rest,
                };
                IRBody::VDecl {
                    var,
                    ty,
                    value,
                    rest: Box::new(rest),
                }
            }
            IRBody::JDecl {
                jp,
                params,
                body,
                rest,
            } => IRBody::JDecl {
                jp,
                params,
                body: Box::new(self.rewrite(*body)),
                rest: Box::new(self.rewrite(*rest)),
            },
            IRBody::Inc { var, n, rest } => IRBody::Inc {
                var,
                n,
                rest: Box::new(self.rewrite(*rest)),
            },
            IRBody::Dec { var, rest } => IRBody::Dec {
                var,
                rest: Box::new(self.rewrite(*rest)),
            },
            IRBody::Set {
                var,
                idx,
                value,
                rest,
            } => IRBody::Set {
                var,
                idx,
                value,
                rest: Box::new(self.rewrite(*rest)),
            },
            IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
                var,
                tag,
                rest: Box::new(self.rewrite(*rest)),
            },
            IRBody::USet {
                var,
                idx,
                value,
                rest,
            } => IRBody::USet {
                var,
                idx,
                value,
                rest: Box::new(self.rewrite(*rest)),
            },
            IRBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest,
            } => IRBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest: Box::new(self.rewrite(*rest)),
            },
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => IRBody::Case {
                scrutinee,
                alts: alts
                    .into_iter()
                    .map(|a| IRAlt {
                        ctor: a.ctor,
                        body: Box::new(self.rewrite(*a.body)),
                    })
                    .collect(),
                default: default.map(|d| Box::new(self.rewrite(*d))),
            },
            other @ (IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable) => other,
        }
    }
}

/// Whether the cast temp `u` feeds a CONSUMING position of the instruction
/// boxing prefixed it to: skip the sibling prefix casts (`VDecl`s that do not
/// mention `u`) and look at the first statement that does.
fn feeds_consuming_position(u: VarId, rest: &IRBody) -> bool {
    let is_u = |a: &IRArg| matches!(a, IRArg::Var(v) if *v == u);
    let mut cur = rest;
    loop {
        match cur {
            IRBody::VDecl { value, rest, .. } => {
                match value {
                    // The instruction the casts were prefixed to.
                    IRExpr::Apply { args, .. } if args.iter().any(is_u) => return true,
                    // A sibling cast: an unbox/box of another operand, or an
                    // expensive-constant thunk call standing in for a box.
                    IRExpr::Unbox { arg, .. } | IRExpr::Box { arg, .. } if !is_u(arg) => {}
                    IRExpr::Apply { args, .. } if args.is_empty() => {}
                    _ => return false,
                }
                cur = rest;
            }
            IRBody::Ret(arg) => return is_u(arg),
            IRBody::Jmp { args, .. } => return args.iter().any(is_u),
            _ => return false,
        }
    }
}

/// How a domain variable's reference starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Binding {
    /// The binding produces one owned reference.
    Owned,
    /// A field projection: borrowed from the parent. The repair makes it
    /// owned by an `inc` right after the projection (while the parent is
    /// certainly alive) whenever it is used at all.
    Borrowed,
}

/// Uses of domain variables by one instruction.
#[derive(Default)]
struct Uses {
    /// Owned consumptions, with multiplicity.
    consumed: BTreeMap<u32, u32>,
    /// Borrowed reads.
    borrowed: BTreeSet<u32>,
}

struct Repair<'a> {
    domain: BTreeMap<u32, Binding>,
    jp_live: HashMap<JoinPointId, BTreeSet<u32>>,
    sigs: &'a BorrowMap,
}

static EMPTY_SIGS: std::sync::LazyLock<BorrowMap> = std::sync::LazyLock::new(BorrowMap::new);

/// One non-terminal statement of a flattened `let` chain.
enum Stmt<'a> {
    VDecl(VarId, &'a IRType, &'a IRExpr),
    Inc(VarId, u32),
    Dec(VarId),
    Set(VarId, u32, VarId),
    SetTag(VarId, u32),
    USet(VarId, u32, VarId),
    SSet(VarId, u32, u32, VarId, &'a IRType),
    JDecl(JoinPointId, &'a [(VarId, IRType)], IRBody),
}

impl<'a> Repair<'a> {
    fn new(_decl: &IRDecl, domain: BTreeMap<u32, Binding>) -> Self {
        Self {
            domain,
            jp_live: HashMap::new(),
            sigs: &EMPTY_SIGS,
        }
    }

    fn in_domain(&self, v: u32) -> bool {
        self.domain.contains_key(&v)
    }

    fn owned_position(&self, fn_id: &FnId, idx: usize) -> bool {
        self.sigs
            .get(&fn_id.0)
            .map(|b| idx < b.params.len() && b.params[idx] == Ownership::Owned)
            .unwrap_or(true)
    }

    fn consume(&self, uses: &mut Uses, arg: &IRArg) {
        if let IRArg::Var(v) = arg {
            if self.in_domain(v.0) {
                *uses.consumed.entry(v.0).or_insert(0) += 1;
            }
        }
    }

    fn borrow(&self, uses: &mut Uses, v: u32) {
        if self.in_domain(v) {
            uses.borrowed.insert(v);
        }
    }

    fn expr_uses(&self, value: &IRExpr) -> Uses {
        let mut uses = Uses::default();
        match value {
            IRExpr::Ctor { args, .. } | IRExpr::PartialApply { args, .. } => {
                args.iter().for_each(|a| self.consume(&mut uses, a));
            }
            IRExpr::Reuse { var, args, .. } => {
                self.consume(&mut uses, &IRArg::Var(*var));
                args.iter().for_each(|a| self.consume(&mut uses, a));
            }
            IRExpr::Apply { fn_id, args } => {
                for (idx, arg) in args.iter().enumerate() {
                    if self.owned_position(fn_id, idx) {
                        self.consume(&mut uses, arg);
                    } else if let IRArg::Var(v) = arg {
                        self.borrow(&mut uses, v.0);
                    }
                }
            }
            IRExpr::ClosureApply { closure, args } => {
                self.consume(&mut uses, closure);
                args.iter().for_each(|a| self.consume(&mut uses, a));
            }
            IRExpr::Reset(v) => self.consume(&mut uses, &IRArg::Var(*v)),
            IRExpr::Proj { arg, .. }
            | IRExpr::Tag(arg)
            | IRExpr::Box { arg, .. }
            | IRExpr::Unbox { arg, .. } => {
                if let IRArg::Var(v) = arg {
                    self.borrow(&mut uses, v.0);
                }
            }
            IRExpr::UProj { var, .. } | IRExpr::SProj { var, .. } | IRExpr::IsShared(var) => {
                self.borrow(&mut uses, var.0);
            }
            IRExpr::Lit(_) | IRExpr::String(_) => {}
        }
        uses
    }

    /// Rewrite `body`, returning it with its live-in set of domain variables.
    fn body(&mut self, body: &'a IRBody) -> (IRBody, BTreeSet<u32>) {
        let mut stmts: Vec<Stmt<'a>> = Vec::new();
        let mut cur = body;
        let (mut out, mut live) = loop {
            match cur {
                IRBody::VDecl {
                    var,
                    ty,
                    value,
                    rest,
                } => {
                    stmts.push(Stmt::VDecl(*var, ty, value));
                    cur = rest;
                }
                IRBody::Inc { var, n, rest } => {
                    stmts.push(Stmt::Inc(*var, *n));
                    cur = rest;
                }
                IRBody::Dec { var, rest } => {
                    stmts.push(Stmt::Dec(*var));
                    cur = rest;
                }
                IRBody::Set {
                    var,
                    idx,
                    value,
                    rest,
                } => {
                    stmts.push(Stmt::Set(*var, *idx, *value));
                    cur = rest;
                }
                IRBody::SetTag { var, tag, rest } => {
                    stmts.push(Stmt::SetTag(*var, *tag));
                    cur = rest;
                }
                IRBody::USet {
                    var,
                    idx,
                    value,
                    rest,
                } => {
                    stmts.push(Stmt::USet(*var, *idx, *value));
                    cur = rest;
                }
                IRBody::SSet {
                    var,
                    n,
                    offset,
                    value,
                    ty,
                    rest,
                } => {
                    stmts.push(Stmt::SSet(*var, *n, *offset, *value, ty));
                    cur = rest;
                }
                IRBody::JDecl {
                    jp,
                    params,
                    body: jp_body,
                    rest,
                } => {
                    let (new_body, live_in) = self.body(jp_body);
                    self.jp_live.insert(*jp, live_in);
                    stmts.push(Stmt::JDecl(*jp, params, new_body));
                    cur = rest;
                }
                IRBody::Case {
                    scrutinee,
                    alts,
                    default,
                } => break self.case(*scrutinee, alts, default.as_deref()),
                IRBody::Jmp { jp, args } => {
                    let after = self.jp_live.get(jp).cloned().unwrap_or_default();
                    let mut uses = Uses::default();
                    args.iter().for_each(|a| self.consume(&mut uses, a));
                    let mut node = IRBody::Jmp {
                        jp: *jp,
                        args: args.clone(),
                    };
                    node = self.pre_incs(node, &uses, &after);
                    let mut live = after;
                    live.extend(uses.consumed.keys().copied());
                    break (node, live);
                }
                IRBody::Ret(arg) => {
                    let mut live = BTreeSet::new();
                    if let IRArg::Var(v) = arg {
                        if self.in_domain(v.0) {
                            live.insert(v.0);
                        }
                    }
                    break (IRBody::Ret(arg.clone()), live);
                }
                IRBody::Unreachable => break (IRBody::Unreachable, BTreeSet::new()),
            }
        };
        for stmt in stmts.into_iter().rev() {
            (out, live) = self.stmt(stmt, out, live);
        }
        (out, live)
    }

    /// Incs before an instruction that consumes domain variables: one per
    /// consumed occurrence the variable survives (all of them if it stays
    /// live or is also read in a borrowed position of the same instruction).
    fn pre_incs(&self, mut node: IRBody, uses: &Uses, live_after: &BTreeSet<u32>) -> IRBody {
        for (&v, &k) in uses.consumed.iter().rev() {
            let n = if live_after.contains(&v) || uses.borrowed.contains(&v) {
                k
            } else {
                k - 1
            };
            if n > 0 {
                node = IRBody::Inc {
                    var: VarId(v),
                    n,
                    rest: Box::new(node),
                };
            }
        }
        node
    }

    /// Decs right after an instruction for domain variables whose last use
    /// it was a borrowed read.
    fn post_decs(&self, mut rest: IRBody, uses: &Uses, live_after: &BTreeSet<u32>) -> IRBody {
        for &v in uses.borrowed.iter().rev() {
            if !live_after.contains(&v) {
                rest = IRBody::Dec {
                    var: VarId(v),
                    rest: Box::new(rest),
                };
            }
        }
        rest
    }

    fn stmt(&self, stmt: Stmt<'a>, rest: IRBody, live: BTreeSet<u32>) -> (IRBody, BTreeSet<u32>) {
        match stmt {
            Stmt::VDecl(var, ty, value) => {
                let mut live_mid = live;
                let x_live = live_mid.remove(&var.0);
                let uses = self.expr_uses(value);
                let mut after = self.post_decs(rest, &uses, &live_mid);
                match self.domain.get(&var.0) {
                    Some(Binding::Owned) if !x_live => {
                        after = IRBody::Dec {
                            var,
                            rest: Box::new(after),
                        };
                    }
                    Some(Binding::Borrowed) if x_live => {
                        after = IRBody::Inc {
                            var,
                            n: 1,
                            rest: Box::new(after),
                        };
                    }
                    _ => {}
                }
                let node = IRBody::VDecl {
                    var,
                    ty: ty.clone(),
                    value: value.clone(),
                    rest: Box::new(after),
                };
                let node = self.pre_incs(node, &uses, &live_mid);
                let mut live = live_mid;
                live.extend(uses.consumed.keys().copied());
                live.extend(uses.borrowed.iter().copied());
                (node, live)
            }
            Stmt::Set(var, idx, value) => {
                let mut uses = Uses::default();
                self.consume(&mut uses, &IRArg::Var(value));
                self.borrow(&mut uses, var.0);
                let after = self.post_decs(rest, &uses, &live);
                let node = IRBody::Set {
                    var,
                    idx,
                    value,
                    rest: Box::new(after),
                };
                let node = self.pre_incs(node, &uses, &live);
                let mut live = live;
                live.extend(uses.consumed.keys().copied());
                live.extend(uses.borrowed.iter().copied());
                (node, live)
            }
            Stmt::SetTag(var, tag) => {
                self.borrowing(var, rest, live, |rest| IRBody::SetTag { var, tag, rest })
            }
            Stmt::USet(var, idx, value) => self.borrowing(var, rest, live, |rest| IRBody::USet {
                var,
                idx,
                value,
                rest,
            }),
            Stmt::SSet(var, n, offset, value, ty) => {
                self.borrowing(var, rest, live, |rest| IRBody::SSet {
                    var,
                    n,
                    offset,
                    value,
                    ty: ty.clone(),
                    rest,
                })
            }
            Stmt::Inc(var, n) => (
                IRBody::Inc {
                    var,
                    n,
                    rest: Box::new(rest),
                },
                live,
            ),
            Stmt::Dec(var) => (
                IRBody::Dec {
                    var,
                    rest: Box::new(rest),
                },
                live,
            ),
            Stmt::JDecl(jp, params, body) => (
                IRBody::JDecl {
                    jp,
                    params: params.to_vec(),
                    body: Box::new(body),
                    rest: Box::new(rest),
                },
                live,
            ),
        }
    }

    /// An in-place mutation that only READS its target.
    fn borrowing(
        &self,
        var: VarId,
        rest: IRBody,
        live: BTreeSet<u32>,
        build: impl FnOnce(Box<IRBody>) -> IRBody,
    ) -> (IRBody, BTreeSet<u32>) {
        let mut uses = Uses::default();
        self.borrow(&mut uses, var.0);
        let after = self.post_decs(rest, &uses, &live);
        let mut live = live;
        live.extend(uses.borrowed.iter().copied());
        (build(Box::new(after)), live)
    }

    /// A `Case`: each arm starts by releasing the domain variables that are
    /// live into the case but dead in that arm (the scrutinee included).
    fn case(
        &mut self,
        scrutinee: VarId,
        alts: &'a [IRAlt],
        default: Option<&'a IRBody>,
    ) -> (IRBody, BTreeSet<u32>) {
        let arms: Vec<(IRBody, BTreeSet<u32>)> = alts.iter().map(|a| self.body(&a.body)).collect();
        let default_arm = default.map(|d| self.body(d));
        let mut live: BTreeSet<u32> = BTreeSet::new();
        for (_, l) in arms.iter().chain(default_arm.iter()) {
            live.extend(l.iter().copied());
        }
        if self.in_domain(scrutinee.0) {
            live.insert(scrutinee.0);
        }
        let release = |body: IRBody, arm_live: &BTreeSet<u32>| -> IRBody {
            live.iter()
                .rev()
                .filter(|v| !arm_live.contains(v))
                .fold(body, |rest, &v| IRBody::Dec {
                    var: VarId(v),
                    rest: Box::new(rest),
                })
        };
        let new_alts = alts
            .iter()
            .zip(arms)
            .map(|(alt, (body, arm_live))| IRAlt {
                ctor: alt.ctor.clone(),
                body: Box::new(release(body, &arm_live)),
            })
            .collect();
        let new_default = default_arm.map(|(body, arm_live)| Box::new(release(body, &arm_live)));
        (
            IRBody::Case {
                scrutinee,
                alts: new_alts,
                default: new_default,
            },
            live,
        )
    }
}

#[cfg(test)]
#[path = "rc_repair_tests_support.rs"]
pub(crate) mod e2e_support;

#[cfg(test)]
#[path = "rc_repair_tests.rs"]
mod tests;

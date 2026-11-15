// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The RC linearity engine: every object-representation variable of a FINAL
//! (post-boxing) L5IR declaration is linear along every path.
//!
//! This is the one RC path checker in the crate. It backs both the
//! fail-closed pipeline gate [`super::verify_rc_linearity`] and the
//! diagnostic `RcPath` category of the test-only `ir_checker_ext2` checker,
//! which used to count only `Inc`/`Dec` balance and never consumptions (so a
//! value passed twice to a consuming call with no `inc` — the WS6.2 `sqLet`
//! double consume — was invisible to it).
//!
//! # The rule
//!
//! A variable is TRACKED when its IR type is an object type
//! ([`IRType::is_object`]); scalars, `Erased` and `Void` carry no reference.
//! Each tracked variable holds a running count of the references the frame
//! owns through it:
//!
//! * an OWNED binding starts at 1 — an owned parameter, and the result of
//!   `Apply` / `PartialApply` / `ClosureApply` / `Ctor` / `Reuse` / `Reset` /
//!   `Box` / `String` / an object literal, and a projection out of an
//!   unboxed SCALAR carrier (a fresh rebox, see `boxing::visit`);
//! * a BORROWED parameter and a field projection (`Proj` of an object) start
//!   at 0: they are backed by the caller, resp. by the parent object's field
//!   slot, for as long as that backer is alive.
//!
//! `Inc x n` adds `n`. Every OWNED consumption and every `Dec` subtracts 1:
//! an owned position of `Apply` (per the callee's borrow signature, with the
//! same `unwrap_or(true)` owned default as `rc::insert::helpers`), every
//! `PartialApply` / `ClosureApply` argument and the closure itself, `Ctor` /
//! `Reuse` arguments and the reuse slot, `Reset`, a `Set` value, a `Jmp`
//! argument (join-point parameters are owned) and `Ret`. `Proj`, `UProj`,
//! `SProj`, `Tag`, `IsShared`, `Unbox`, a `Case` scrutinee, the target of a
//! `Set*`/`SetTag` and a borrowed `Apply` position are BORROWED reads.
//!
//! Along every path: the count never goes below zero, every use (borrowed
//! uses and `Inc` included) happens while the variable still holds or is
//! backed by a reference (no use after the final consumption), and at `Ret`
//! — and when a variable leaves scope at a jump — every count is 0. For an
//! owned binding that is exactly `#owned-consumptions + #Dec = 1 + #Inc`;
//! for a borrowed one `#owned-consumptions + #Dec = #Inc`. `Unreachable`
//! ends a path with no obligation (panic = abort).
//!
//! # Reset/reuse fast paths
//!
//! `rc::expand` lowers `reset`/`reuse` into an `isShared` test whose FAST
//! path steals field references out of the exclusive object instead of
//! `inc`ing the projections (Lean's `eraseProjIncFor`), overwrites the
//! stolen slots with `Set`, and releases unread fields with `proj + dec`.
//! The engine models exactly that and nothing looser: on the branch where
//! `IsShared(x)` is known to be `0` (the value flows through join-point
//! arguments), `x`'s object is EXCLUSIVE, and a zero-count projection of an
//! exclusive object may be consumed or `Dec`'d once per field slot — the
//! slot is then TAKEN. A taken slot must be overwritten by `Set` before the
//! object is released, handed away, `inc`ed or passed to a borrowing callee
//! — even while the frame keeps another reference (the runtime would
//! otherwise release the field a second time, or a new holder would read a
//! field object the frame already gave away); only a move into a join point
//! keeps it in the frame. A `Set` over a slot that was not taken
//! overwrites a reference nobody released. A projection that took its slot
//! is spent (it gave away the one reference it could reach), and once `Set`
//! refills a slot every projection of it still names the OLD field object,
//! so it holds only the references it was `inc`ed. An `inc` of the object
//! also invalidates an earlier `IsShared` answer about it. Branch values are
//! tracked only to prune infeasible `Case` arms; nothing else is inferred
//! from them.
//!
//! Malformed shapes the analysis cannot attribute are refused outright: a
//! join-point id declared twice, a jump whose argument count differs from
//! the join point's parameter count, a tracked object passed to a NON-object
//! join-point parameter (its reference would be dropped), and a binding that
//! reuses the id of a variable still holding references (they would be
//! overwritten, never released).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId};
use crate::rc::borrow::{BorrowMap, Ownership};

/// Upper bound on statement visits per declaration. Join-point bodies are
/// memoized per entry state, so honest code stays far below this; a
/// declaration that exceeds it is refused (fail closed), never waved through.
const VISIT_BUDGET: usize = 4_000_000;

pub(crate) use super::RcLinearityViolation;

/// Where a tracked variable's reference comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Origin {
    /// The frame owns one reference at the binding.
    Owned,
    /// A borrowed parameter: backed by the caller for the whole body.
    BorrowedParam,
    /// A field projection: backed by the parent object's slot `idx`.
    Field { parent: u32, idx: u32 },
    /// An erased / null placeholder: RC operations on it are no-ops.
    Null,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Slot {
    /// Object identity (the binding var; join-point params inherit it).
    obj: u32,
    origin: Origin,
    count: i64,
    consumed: u32,
    incs: u32,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct State {
    vars: BTreeMap<u32, Slot>,
    /// Known scalar values (branch facts), used only to prune `Case` arms.
    known: BTreeMap<u32, u64>,
    /// `r := IsShared(x)`: `r` → `x`'s object.
    shared_probe: BTreeMap<u32, u32>,
    /// Objects known to be uniquely referenced (their `IsShared` was 0).
    exclusive: BTreeSet<u32>,
    /// Field slots `(object, idx)` whose reference a projection took.
    taken: BTreeSet<(u32, u32)>,
}

struct JpDef<'a> {
    params: &'a [(VarId, IRType)],
    body: &'a IRBody,
    scope: BTreeSet<u32>,
}

struct Walker<'a> {
    decl: String,
    sigs: &'a BorrowMap,
    types: HashMap<u32, IRType>,
    jps: HashMap<JoinPointId, JpDef<'a>>,
    memo: HashSet<(u32, State)>,
    budget: usize,
    /// A join-point id declared twice in one body: the id → body map would
    /// analyse the wrong body at one of them, so the declaration is refused.
    duplicate_jp: Option<JoinPointId>,
}

/// Check one declaration against the linearity rule, with the callee and
/// parameter borrow signatures in `sigs` (the pipeline's all-owned ABI is an
/// empty map: every position of every callee defaults to owned).
pub(crate) fn check_decl(decl: &IRDecl, sigs: &BorrowMap) -> Result<(), RcLinearityViolation> {
    let mut walker = Walker {
        decl: decl.name.to_string(),
        sigs,
        types: HashMap::new(),
        jps: HashMap::new(),
        memo: HashSet::new(),
        budget: VISIT_BUDGET,
        duplicate_jp: None,
    };
    let mut bound: Vec<u32> = Vec::new();
    for (var, ty) in &decl.params {
        walker.types.insert(var.0, ty.clone());
        bound.push(var.0);
    }
    walker.collect(&decl.body, &mut bound);
    if let Some(jp) = walker.duplicate_jp {
        return Err(RcLinearityViolation {
            decl: walker.decl,
            var: 0,
            consumed: 0,
            incs: 0,
            path: "entry".to_string(),
            detail: format!(
                "join point jp{} is declared more than once; jumps to it cannot be \
                 attributed to one body, so the declaration is refused",
                jp.0
            ),
        });
    }

    let own_sig = sigs.get(&decl.name);
    let mut st = State::default();
    for (idx, (var, ty)) in decl.params.iter().enumerate() {
        if !ty.is_object() {
            continue;
        }
        // Mirrors `rc::insert::insert_rc`: a declaration with borrow info
        // reads `params[idx]`, defaulting to owned past its end; no borrow
        // info at all means all-owned.
        let ownership = own_sig
            .map(|b| b.params.get(idx).copied().unwrap_or(Ownership::Owned))
            .unwrap_or(Ownership::Owned);
        let (origin, count) = match ownership {
            Ownership::Owned => (Origin::Owned, 1),
            Ownership::Borrowed => (Origin::BorrowedParam, 0),
        };
        st.vars.insert(
            var.0,
            Slot {
                obj: var.0,
                origin,
                count,
                consumed: 0,
                incs: 0,
            },
        );
    }
    walker.walk(&decl.body, st, "entry".to_string())
}

impl<'a> Walker<'a> {
    /// Pre-pass: record every variable's IR type and every join point's
    /// lexical scope (the variables bound before its declaration).
    fn collect(&mut self, body: &'a IRBody, bound: &mut Vec<u32>) {
        let mark = bound.len();
        let mut cur = body;
        loop {
            match cur {
                IRBody::VDecl { var, ty, rest, .. } => {
                    self.types.insert(var.0, ty.clone());
                    bound.push(var.0);
                    cur = rest;
                }
                IRBody::Inc { rest, .. }
                | IRBody::Dec { rest, .. }
                | IRBody::Set { rest, .. }
                | IRBody::SetTag { rest, .. }
                | IRBody::USet { rest, .. }
                | IRBody::SSet { rest, .. } => cur = rest,
                IRBody::JDecl {
                    jp,
                    params,
                    body: jp_body,
                    rest,
                } => {
                    let previous = self.jps.insert(
                        *jp,
                        JpDef {
                            params,
                            body: jp_body,
                            scope: bound.iter().copied().collect(),
                        },
                    );
                    if previous.is_some() && self.duplicate_jp.is_none() {
                        self.duplicate_jp = Some(*jp);
                    }
                    let inner = bound.len();
                    for (var, ty) in params {
                        self.types.insert(var.0, ty.clone());
                        bound.push(var.0);
                    }
                    self.collect(jp_body, bound);
                    bound.truncate(inner);
                    cur = rest;
                }
                IRBody::Case { alts, default, .. } => {
                    for alt in alts {
                        self.collect(&alt.body, bound);
                    }
                    if let Some(default) = default {
                        self.collect(default, bound);
                    }
                    break;
                }
                IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => break,
            }
        }
        bound.truncate(mark);
    }

    fn violation(&self, st: &State, var: u32, path: &str, detail: String) -> RcLinearityViolation {
        let (consumed, incs) = st
            .vars
            .get(&var)
            .map(|s| (s.consumed, s.incs))
            .unwrap_or((0, 0));
        RcLinearityViolation {
            decl: self.decl.clone(),
            var,
            consumed,
            incs,
            path: path.to_string(),
            detail,
        }
    }

    fn tick(&mut self, path: &str) -> Result<(), RcLinearityViolation> {
        if self.budget == 0 {
            return Err(RcLinearityViolation {
                decl: self.decl.clone(),
                var: 0,
                consumed: 0,
                incs: 0,
                path: path.to_string(),
                detail: format!(
                    "the linearity analysis exceeded its budget of {VISIT_BUDGET} visits \
                     ({} memoized join-point states); refused rather than assumed linear",
                    self.memo.len()
                ),
            });
        }
        self.budget -= 1;
        Ok(())
    }

    fn walk(
        &mut self,
        body: &'a IRBody,
        mut st: State,
        path: String,
    ) -> Result<(), RcLinearityViolation> {
        let mut cur = body;
        loop {
            self.tick(&path)?;
            match cur {
                IRBody::VDecl {
                    var,
                    ty,
                    value,
                    rest,
                } => {
                    self.vdecl(&mut st, *var, ty, value, &path)?;
                    cur = rest;
                }
                IRBody::Inc { var, n, rest } => {
                    self.inc(&mut st, var.0, *n, &path)?;
                    cur = rest;
                }
                IRBody::Dec { var, rest } => {
                    self.release(&mut st, var.0, &path, Release::Dec)?;
                    cur = rest;
                }
                IRBody::Set {
                    var,
                    idx,
                    value,
                    rest,
                } => {
                    self.set(&mut st, var.0, *idx, value.0, &path)?;
                    cur = rest;
                }
                IRBody::SetTag { var, rest, .. }
                | IRBody::USet { var, rest, .. }
                | IRBody::SSet { var, rest, .. } => {
                    self.borrow_use(&st, var.0, &path, "mutated in place")?;
                    cur = rest;
                }
                IRBody::JDecl { rest, .. } => {
                    // The body is analysed at each jump, from the jump's state.
                    cur = rest;
                }
                IRBody::Case {
                    scrutinee,
                    alts,
                    default,
                } => {
                    self.borrow_use(&st, scrutinee.0, &path, "cased on")?;
                    let s = scrutinee.0;
                    if let Some(&value) = st.known.get(&s) {
                        // A known value selects exactly one arm.
                        if let Some(alt) = alts.iter().find(|a| u64::from(a.ctor.tag) == value) {
                            return self.walk(&alt.body, st, format!("{path}/alt{value}"));
                        }
                        if let Some(default) = default {
                            return self.walk(default, st, format!("{path}/default"));
                        }
                        return Ok(());
                    }
                    for alt in alts {
                        let mut arm = st.clone();
                        let tag = u64::from(alt.ctor.tag);
                        if !arm.vars.contains_key(&s) {
                            arm.known.insert(s, tag);
                        }
                        if tag == 0 {
                            if let Some(&obj) = arm.shared_probe.get(&s) {
                                if frame_holds_obj(&arm, obj) {
                                    arm.exclusive.insert(obj);
                                }
                            }
                        }
                        self.walk(&alt.body, arm, format!("{path}/alt{tag}"))?;
                    }
                    if let Some(default) = default {
                        self.walk(default, st, format!("{path}/default"))?;
                    }
                    return Ok(());
                }
                IRBody::Jmp { jp, args } => return self.jump(st, *jp, args, &path),
                IRBody::Ret(arg) => {
                    if let IRArg::Var(v) = arg {
                        self.release(&mut st, v.0, &path, Release::Consume("returned"))?;
                    }
                    return self.end_of_life(
                        &st,
                        st.vars.keys().copied().collect(),
                        &path,
                        "at return",
                    );
                }
                IRBody::Unreachable => return Ok(()),
            }
        }
    }

    fn vdecl(
        &mut self,
        st: &mut State,
        var: VarId,
        ty: &IRType,
        value: &IRExpr,
        path: &str,
    ) -> Result<(), RcLinearityViolation> {
        let mut origin = Origin::Owned;
        match value {
            IRExpr::Ctor { args, .. } => {
                self.consume_args(st, args, path, "stored in a constructor")?;
            }
            IRExpr::Reuse {
                var: slot, args, ..
            } => {
                self.release(st, slot.0, path, Release::Consume("reused"))?;
                self.consume_args(st, args, path, "stored in a reused constructor")?;
            }
            IRExpr::Proj { idx, arg, .. } => match arg {
                IRArg::Var(parent) => {
                    self.borrow_use(st, parent.0, path, "projected from")?;
                    origin = match st.vars.get(&parent.0) {
                        Some(p) if p.origin == Origin::Null => Origin::Null,
                        Some(p) => Origin::Field {
                            parent: p.obj,
                            idx: *idx,
                        },
                        // A projection out of an unboxed scalar carrier is a
                        // fresh, owned rebox (`boxing::visit`).
                        None if self.types.get(&parent.0).is_some_and(IRType::is_scalar) => {
                            Origin::Owned
                        }
                        None => Origin::Null,
                    };
                }
                IRArg::Erased => origin = Origin::Null,
            },
            IRExpr::Tag(arg) | IRExpr::Unbox { arg, .. } | IRExpr::Box { arg, .. } => {
                if let IRArg::Var(v) = arg {
                    self.borrow_use(st, v.0, path, "read")?;
                }
            }
            IRExpr::UProj { var: v, .. } | IRExpr::SProj { var: v, .. } => {
                self.borrow_use(st, v.0, path, "read")?;
            }
            IRExpr::IsShared(v) => {
                self.borrow_use(st, v.0, path, "tested for sharing")?;
                if let Some(obj) = st.vars.get(&v.0).map(|s| s.obj) {
                    st.shared_probe.insert(var.0, obj);
                }
            }
            IRExpr::Lit(lit) => {
                if let Some(value) = literal_value(lit) {
                    st.known.insert(var.0, value);
                }
            }
            IRExpr::String(_) => {}
            IRExpr::Apply { fn_id, args } => {
                // Owned positions are consumed first; borrowed positions are
                // read DURING the call, so they must still be held after the
                // owned arguments were handed over.
                let mut borrowed = Vec::new();
                for (idx, arg) in args.iter().enumerate() {
                    if let IRArg::Var(v) = arg {
                        if self.callee_position_owned(fn_id, idx) {
                            self.release(
                                st,
                                v.0,
                                path,
                                Release::Consume("passed to an owned parameter"),
                            )?;
                        } else {
                            borrowed.push(v.0);
                        }
                    }
                }
                for v in borrowed {
                    self.borrow_use(st, v, path, "passed to a borrowed parameter")?;
                    let obj = st.vars.get(&v).map(|s| s.obj);
                    if let Some(idx) = obj.and_then(|obj| taken_slot(st, obj)) {
                        return Err(self.violation(
                            st,
                            v,
                            path,
                            format!(
                                "passed to a borrowed parameter while field {idx}'s reference was \
                                 taken by a projection and not yet overwritten (the callee would \
                                 read a field object the frame gave away)"
                            ),
                        ));
                    }
                }
            }
            IRExpr::PartialApply { args, .. } => {
                self.consume_args(st, args, path, "captured by a partial application")?;
            }
            IRExpr::ClosureApply { closure, args } => {
                if let IRArg::Var(v) = closure {
                    self.release(st, v.0, path, Release::Consume("applied as a closure"))?;
                }
                self.consume_args(st, args, path, "passed to a closure")?;
            }
            IRExpr::Reset(v) => {
                self.release(st, v.0, path, Release::Consume("reset"))?;
            }
        }
        self.refuse_rebinding(st, var.0, path)?;
        if ty.is_object() {
            // An object-typed literal (a tagged small value) is owned, like
            // every other freshly produced object.
            let count = i64::from(origin == Origin::Owned);
            st.vars.insert(
                var.0,
                Slot {
                    obj: var.0,
                    origin,
                    count,
                    consumed: 0,
                    incs: 0,
                },
            );
        }
        Ok(())
    }

    /// A binding (or a join-point parameter) that reuses the id of a
    /// variable still holding references would overwrite that count: the
    /// references it held are never released.
    fn refuse_rebinding(
        &self,
        st: &State,
        var: u32,
        path: &str,
    ) -> Result<(), RcLinearityViolation> {
        match st.vars.get(&var) {
            Some(slot) if slot.origin != Origin::Null && slot.count != 0 => Err(self.violation(
                st,
                var,
                path,
                format!(
                    "rebound while it still holds {} reference(s) (a leak: the earlier binding's \
                     references are never released)",
                    slot.count
                ),
            )),
            _ => Ok(()),
        }
    }

    fn callee_position_owned(&self, fn_id: &FnId, idx: usize) -> bool {
        // Same default as `rc::insert::helpers::process_let_value`.
        self.sigs
            .get(&fn_id.0)
            .map(|b| idx < b.params.len() && b.params[idx] == Ownership::Owned)
            .unwrap_or(true)
    }

    fn consume_args(
        &self,
        st: &mut State,
        args: &[IRArg],
        path: &str,
        what: &'static str,
    ) -> Result<(), RcLinearityViolation> {
        for arg in args {
            if let IRArg::Var(v) = arg {
                self.release(st, v.0, path, Release::Consume(what))?;
            }
        }
        Ok(())
    }

    fn borrow_use(
        &self,
        st: &State,
        var: u32,
        path: &str,
        what: &str,
    ) -> Result<(), RcLinearityViolation> {
        match st.vars.get(&var) {
            Some(slot) if !holds(st, slot, 0) => Err(self.violation(
                st,
                var,
                path,
                format!("{what} after its last reference was released (use after the final consumption)"),
            )),
            _ => Ok(()),
        }
    }

    fn inc(
        &self,
        st: &mut State,
        var: u32,
        n: u32,
        path: &str,
    ) -> Result<(), RcLinearityViolation> {
        let Some(slot) = st.vars.get(&var) else {
            return Ok(());
        };
        if slot.origin == Origin::Null {
            return Ok(());
        }
        if !holds(st, slot, 0) {
            return Err(self.violation(
                st,
                var,
                path,
                "inc after its last reference was released".to_string(),
            ));
        }
        let obj = slot.obj;
        if let Some(idx) = taken_slot(st, obj) {
            // Sharing an object whose slot a projection emptied would hand
            // the new holder a field reference the frame already gave away.
            return Err(self.violation(
                st,
                var,
                path,
                format!(
                    "inc while field {idx}'s reference was taken by a projection and not yet \
                     overwritten (the object would be shared with a field it does not own)"
                ),
            ));
        }
        if let Some(slot) = st.vars.get_mut(&var) {
            slot.count += i64::from(n);
            slot.incs += n;
        }
        st.exclusive.remove(&obj);
        // An `IsShared` answer computed BEFORE this `inc` is stale: the object
        // now has a second reference, so a later `case` on that answer must
        // not mark it exclusive.
        st.shared_probe.retain(|_, probed| *probed != obj);
        Ok(())
    }

    /// An owned consumption or a `Dec` of `var`.
    fn release(
        &self,
        st: &mut State,
        var: u32,
        path: &str,
        how: Release,
    ) -> Result<(), RcLinearityViolation> {
        let Some(slot) = st.vars.get(&var).cloned() else {
            return Ok(());
        };
        if slot.origin == Origin::Null {
            return Ok(());
        }
        if !matches!(how, Release::Dec) {
            if let Some(s) = st.vars.get_mut(&var) {
                s.consumed += 1;
            }
        }
        if slot.count >= 1 {
            if let Some(s) = st.vars.get_mut(&var) {
                s.count -= 1;
            }
            if !matches!(how, Release::Move) {
                self.check_taken_fields(st, var, slot.obj, path)?;
            }
            return Ok(());
        }
        match slot.origin {
            Origin::BorrowedParam => Err(self.violation(
                st,
                var,
                path,
                match how {
                    Release::Dec => "dec of a borrowed parameter, which holds no reference".to_string(),
                    Release::Consume(what) => format!("{what}: a borrowed parameter holds no reference to give"),
                    Release::Move => "passed to a join point: a borrowed parameter holds no reference to give".to_string(),
                },
            )),
            Origin::Field { parent, idx }
                if st.exclusive.contains(&parent)
                    && !st.taken.contains(&(parent, idx))
                    && frame_holds_obj(st, parent) =>
            {
                // Fast path: the field's reference is taken out of the
                // exclusive parent's slot (Lean's `eraseProjIncFor`). The
                // projection has now given away the one reference it could
                // reach: it is spent, and a later `Set` that refills the slot
                // must not make it usable (or takeable) again.
                st.taken.insert((parent, idx));
                if let Some(s) = st.vars.get_mut(&var) {
                    s.origin = Origin::Owned;
                }
                Ok(())
            }
            _ => Err(self.violation(
                st,
                var,
                path,
                match how {
                    Release::Dec => "dec with no reference left to release (over-release)".to_string(),
                    Release::Consume(what) => {
                        format!("{what} with no reference left to give (a duplicate consumption needs an inc)")
                    }
                    Release::Move => {
                        "passed to a join point with no reference left to give".to_string()
                    }
                },
            )),
        }
    }

    /// After a reference of `obj` was released or handed away: if a
    /// projection TOOK one of its field slots and no `Set` refilled it, the
    /// reference just released reaches an object whose field the frame no
    /// longer owns — whoever releases the object releases that field again,
    /// and whoever received it (the frame may still hold another reference)
    /// reads a field object that was given away. Only a MOVE into a join
    /// point keeps the object in the frame (same identity, same taken set).
    fn check_taken_fields(
        &self,
        st: &State,
        var: u32,
        obj: u32,
        path: &str,
    ) -> Result<(), RcLinearityViolation> {
        if let Some(idx) = taken_slot(st, obj) {
            return Err(self.violation(
                st,
                var,
                path,
                format!(
                    "released while field {idx}'s reference was taken by a projection and never \
                     overwritten (the field would be released twice)"
                ),
            ));
        }
        Ok(())
    }

    fn set(
        &self,
        st: &mut State,
        var: u32,
        idx: u32,
        value: u32,
        path: &str,
    ) -> Result<(), RcLinearityViolation> {
        self.borrow_use(st, var, path, "mutated in place")?;
        self.release(st, value, path, Release::Consume("stored into a field"))?;
        let Some(obj) = st.vars.get(&var).map(|s| s.obj) else {
            return Ok(());
        };
        if st.taken.remove(&(obj, idx)) {
            // Every projection of the overwritten slot still names the OLD
            // field object, which the slot no longer backs: from here on
            // such a variable holds only the references it was `inc`ed.
            for slot in st.vars.values_mut() {
                if slot.origin == (Origin::Field { parent: obj, idx }) {
                    slot.origin = Origin::Owned;
                }
            }
            return Ok(());
        }
        let detail = if st.exclusive.contains(&obj) {
            format!("field {idx} is overwritten without releasing the reference it held")
        } else {
            format!("field {idx} is overwritten on an object not known to be exclusive")
        };
        Err(self.violation(st, var, path, detail))
    }

    fn jump(
        &mut self,
        mut st: State,
        jp: JoinPointId,
        args: &[IRArg],
        path: &str,
    ) -> Result<(), RcLinearityViolation> {
        let Some(def) = self.jps.get(&jp) else {
            return Err(RcLinearityViolation {
                decl: self.decl.clone(),
                var: 0,
                consumed: 0,
                incs: 0,
                path: path.to_string(),
                detail: format!("jump to undeclared join point jp{}", jp.0),
            });
        };
        let params = def.params;
        let body = def.body;
        let scope = def.scope.clone();
        if args.len() != params.len() {
            // A missing argument would enter as an untracked placeholder and
            // an extra one would never be handed over: neither is analysable.
            return Err(RcLinearityViolation {
                decl: self.decl.clone(),
                var: 0,
                consumed: 0,
                incs: 0,
                path: path.to_string(),
                detail: format!(
                    "jump to jp{} passes {} argument(s) for {} parameter(s)",
                    jp.0,
                    args.len(),
                    params.len()
                ),
            });
        }

        let mut entering: Vec<(u32, Option<Slot>, Option<u64>, Option<u32>)> = Vec::new();
        for (i, (param, pty)) in params.iter().enumerate() {
            let arg = args[i].clone();
            let (slot, known, probe) = match arg {
                IRArg::Var(a) => {
                    let known = st.known.get(&a.0).copied();
                    let probe = st.shared_probe.get(&a.0).copied();
                    match st.vars.get(&a.0).cloned() {
                        Some(src) if src.origin != Origin::Null && !pty.is_object() => {
                            // The reference would be handed to a parameter
                            // that carries none: dropped, and the pointer read
                            // as a scalar.
                            return Err(self.violation(
                                &st,
                                a.0,
                                path,
                                format!(
                                    "passed to jp{}'s non-object parameter %{} (its reference \
                                     would be dropped)",
                                    jp.0, param.0
                                ),
                            ));
                        }
                        Some(src) => {
                            self.release(&mut st, a.0, path, Release::Move)?;
                            let origin = if src.origin == Origin::Null {
                                Origin::Null
                            } else {
                                Origin::Owned
                            };
                            let slot = pty.is_object().then_some(Slot {
                                obj: src.obj,
                                origin,
                                count: i64::from(origin == Origin::Owned),
                                consumed: 0,
                                incs: 0,
                            });
                            (slot, known, probe)
                        }
                        None => (null_slot(param.0, pty), known, probe),
                    }
                }
                IRArg::Erased => (null_slot(param.0, pty), None, None),
            };
            entering.push((param.0, slot, known, probe));
        }

        // Variables bound after the join point's declaration leave scope here.
        let leaving: Vec<u32> = st
            .vars
            .keys()
            .copied()
            .filter(|v| !scope.contains(v))
            .collect();
        self.end_of_life(
            &st,
            leaving.clone(),
            path,
            &format!("when it leaves scope at the jump to jp{}", jp.0),
        )?;
        for v in leaving {
            st.vars.remove(&v);
        }
        st.known.retain(|v, _| scope.contains(v));
        st.shared_probe.retain(|v, _| scope.contains(v));
        for (param, slot, known, probe) in entering {
            self.refuse_rebinding(&st, param, path)?;
            if let Some(slot) = slot {
                st.vars.insert(param, slot);
            }
            if let Some(known) = known {
                st.known.insert(param, known);
            }
            if let Some(probe) = probe {
                st.shared_probe.insert(param, probe);
            }
        }
        if !self.memo.insert((jp.0, st.clone())) {
            return Ok(());
        }
        self.walk(body, st, format!("{path}/jp{}", jp.0))
    }

    fn end_of_life(
        &self,
        st: &State,
        vars: Vec<u32>,
        path: &str,
        when: &str,
    ) -> Result<(), RcLinearityViolation> {
        for v in vars {
            if let Some(slot) = st.vars.get(&v) {
                if slot.origin != Origin::Null && slot.count != 0 {
                    return Err(self.violation(
                        st,
                        v,
                        path,
                        format!(
                            "{} reference(s) never released {when} (a leak: the object is never consumed or dec'd)",
                            slot.count
                        ),
                    ));
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum Release {
    Dec,
    Consume(&'static str),
    Move,
}

fn null_slot(param: u32, ty: &IRType) -> Option<Slot> {
    ty.is_object().then_some(Slot {
        obj: param,
        origin: Origin::Null,
        count: 0,
        consumed: 0,
        incs: 0,
    })
}

/// Whether the variable's slot still holds or is backed by a reference.
fn holds(st: &State, slot: &Slot, depth: u32) -> bool {
    match slot.origin {
        Origin::Null | Origin::BorrowedParam => true,
        _ if slot.count >= 1 => true,
        Origin::Field { parent, idx } => {
            depth < 64 && !st.taken.contains(&(parent, idx)) && obj_alive(st, parent, depth + 1)
        }
        Origin::Owned => false,
    }
}

/// Whether some in-scope variable still holds or is backed by `obj`.
fn obj_alive(st: &State, obj: u32, depth: u32) -> bool {
    st.vars
        .values()
        .any(|s| s.obj == obj && s.origin != Origin::Null && holds(st, s, depth))
}

/// A field slot of `obj` that a projection took and no `Set` refilled yet.
fn taken_slot(st: &State, obj: u32) -> Option<u32> {
    st.taken
        .iter()
        .find(|(o, _)| *o == obj)
        .map(|(_, idx)| *idx)
}

/// Whether the frame itself OWNS a reference to `obj` (a positive count).
fn frame_holds_obj(st: &State, obj: u32) -> bool {
    st.vars.values().any(|s| s.obj == obj && s.count >= 1)
}

fn literal_value(lit: &IRLiteral) -> Option<u64> {
    match lit {
        IRLiteral::Bool(b) => Some(u64::from(*b)),
        IRLiteral::UInt8(v) => Some(u64::from(*v)),
        IRLiteral::UInt16(v) => Some(u64::from(*v)),
        IRLiteral::UInt32(v) => Some(u64::from(*v)),
        IRLiteral::UInt64(v) => Some(*v),
        IRLiteral::USize(v) => Some(*v as u64),
        IRLiteral::NatBig(_) | IRLiteral::Float32(_) | IRLiteral::Float64(_) => None,
    }
}

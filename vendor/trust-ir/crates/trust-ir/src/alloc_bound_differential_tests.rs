//! The whole analysis against the reference interpreter, on random programs.
//!
//! Each program is built twice from one random draw. In the LINT twin every
//! leaf block allocates `count` elements of a known size; in the ORACLE twin
//! the same leaf returns `(site, count)` instead. The interpreter runs the
//! oracle twin on many arguments, and every execution that reaches a site with
//! a defined count (positive; a zero or negative count is UB at the
//! allocation) is held to the lint's verdict on that site:
//!
//! * not reported — `count × size` is within the target's largest object;
//! * [`AllocBoundReason::ExceedsObjectLimit`] — it is not, and `count` is at
//!   least the finding's least count.
//!
//! The programs have the shapes the analysis reasons about: diamonds and joins
//! with block arguments (parallel `CondBr` edges included), switches, loops
//! with a back edge, `select`, unsigned and signed `Overflow` flags, `Assume`,
//! `Assert`, every integer cast and width, and the blocks stored in shuffled
//! order. Element sizes are chosen near `isize::MAX / count`, so a bound that
//! is off by a little crosses the line.
//!
//! Metamorphic half: the lint twin is also judged on targets OUTSIDE the
//! canonical scalar-alignment table with the same pointer width (i686, armv7,
//! powerpc64le, s390x), where the interpreter cannot run. A size needs no
//! alignment, so the verdicts must be identical.
//!
//! The gate runs a fixed seed range; `TRUST_IR_ALLOC_BOUND_PROGRAMS` (and
//! `TRUST_IR_ALLOC_BOUND_SEED`) run more. The non-vacuity counters are
//! asserted: executions reached, executions at unreported sites whose bound
//! came from the analysis (the count's type alone would cross the line), and
//! executions above half the line.

use super::*;
use crate::inst::AssertKind;
use crate::interpret::{
    InterpretInt, InterpretOptions, InterpretValue, InterpretValueKind, Interpreter,
};
use crate::ty::{FuncTy, StructDef};
use crate::value::FuncId;
use crate::{Block, SwitchCase, TargetInfo};

/// xorshift64: deterministic per seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }

    fn pct(&mut self, p: u64) -> bool {
        self.below(100) < p
    }

    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
}

const TYS: [Ty; 12] = [
    Ty::U8,
    Ty::I8,
    Ty::U16,
    Ty::I16,
    Ty::U32,
    Ty::I32,
    Ty::U64,
    Ty::I64,
    Ty::Usize,
    Ty::Isize,
    Ty::U128,
    Ty::I128,
];

/// One allocation site: the leaf block, its count's type and its element's
/// byte size.
struct Site {
    block: u32,
    count_ty: Ty,
    elem: u128,
}

#[derive(Clone)]
struct Scope {
    ints: Vec<(u32, Ty)>,
    bools: Vec<u32>,
}

struct Gen {
    rng: Rng,
    pointer_bits: u32,
    next_val: u32,
    next_block: u32,
    lint_blocks: Vec<Block>,
    oracle_blocks: Vec<Block>,
    sites: Vec<Site>,
    /// A per-program pivot value the constants and arguments cluster around.
    pivot: u128,
    u8_ty: TyId,
    /// A struct with a declared size, for struct-element sites.
    struct_ty: (Ty, u128),
    budget: u32,
}

fn signed(ty: &Ty) -> bool {
    ty.is_signed()
}

impl Gen {
    fn bits(&self, ty: &Ty) -> u32 {
        ty.bit_width_with(self.pointer_bits)
            .expect("an integer type")
    }

    fn limit(&self) -> u128 {
        max_object_bytes(self.pointer_bits)
    }

    fn val(&mut self) -> u32 {
        self.next_val += 1;
        self.next_val
    }

    fn blk(&mut self) -> u32 {
        self.next_block += 1;
        self.next_block
    }

    fn interesting(&mut self, ty: &Ty) -> u128 {
        let m = umax(self.bits(ty));
        let b = self.pivot & m;
        let s = m >> 1;
        let wide = (u128::from(self.rng.next()) << 64 | u128::from(self.rng.next())) & m;
        let choices = [
            0,
            1,
            2,
            3,
            7,
            8,
            255,
            256,
            b.wrapping_sub(1) & m,
            b,
            (b + 1) & m,
            b / 2,
            b.wrapping_mul(2) & m,
            s,
            (s + 1) & m,
            m,
            m - 1,
            u128::from(self.rng.next()) & m,
            u128::from(self.rng.below(64)) & m,
            wide,
        ];
        *self.rng.pick(&choices)
    }

    /// `raw` (bits at `ty`'s width) as the canonical constant of `ty`.
    fn constant(&self, ty: &Ty, raw: u128) -> Constant {
        if signed(ty) {
            Constant::Int(to_signed(raw, self.bits(ty)))
        } else {
            Constant::u128(raw)
        }
    }

    fn konst(&mut self, body: &mut Vec<InstrNode>, ty: &Ty) -> u32 {
        let r = self.val();
        let raw = self.interesting(ty);
        let value = self.constant(ty, raw);
        body.push(
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value,
            })
            .with_result(ValueId::new(r)),
        );
        r
    }

    fn of_ty(&mut self, sc: &Scope, body: &mut Vec<InstrNode>, ty: &Ty) -> u32 {
        let same: Vec<u32> = sc
            .ints
            .iter()
            .filter(|(_, t)| t == ty)
            .map(|(v, _)| *v)
            .collect();
        if !same.is_empty() && self.rng.pct(70) {
            *self.rng.pick(&same)
        } else {
            self.konst(body, ty)
        }
    }

    fn icmp(&mut self, sc: &mut Scope, body: &mut Vec<InstrNode>) -> u32 {
        let (a, ty) = if sc.ints.is_empty() || self.rng.pct(10) {
            let ty = self.rng.pick(&TYS).clone();
            (self.konst(body, &ty), ty)
        } else {
            self.rng.pick(&sc.ints).clone()
        };
        let other = self.of_ty(sc, body, &ty);
        let ops = [
            ICmpOp::Eq,
            ICmpOp::Ne,
            ICmpOp::Ult,
            ICmpOp::Ule,
            ICmpOp::Ugt,
            ICmpOp::Uge,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
        ];
        let op = *self.rng.pick(&ops);
        let (lhs, rhs) = if self.rng.pct(50) {
            (a, other)
        } else {
            (other, a)
        };
        let c = self.val();
        body.push(
            InstrNode::new(Inst::ICmp {
                op,
                ty,
                lhs: ValueId::new(lhs),
                rhs: ValueId::new(rhs),
            })
            .with_result(ValueId::new(c)),
        );
        sc.bools.push(c);
        c
    }

    fn cond(&mut self, sc: &mut Scope, body: &mut Vec<InstrNode>) -> u32 {
        if sc.bools.is_empty() || !self.rng.pct(50) {
            return self.icmp(sc, body);
        }
        let c = *self.rng.pick(&sc.bools);
        let wrap = match self.rng.below(10) {
            // Boolean negation in its one spelling, `bxor %c, true`
            // (SPEC_RATIFICATIONS §3.2), in either operand order; `false`
            // keeps the condition.
            0 | 1 => {
                let k = self.val();
                let flip = self.rng.pct(75);
                body.push(
                    InstrNode::new(Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(flip),
                    })
                    .with_result(ValueId::new(k)),
                );
                let (lhs, rhs) = if self.rng.pct(50) { (c, k) } else { (k, c) };
                Some(Inst::BinOp {
                    op: BinOp::BXor,
                    ty: Ty::Bool,
                    lhs: ValueId::new(lhs),
                    rhs: ValueId::new(rhs),
                })
            }
            2 => Some(Inst::Copy {
                ty: Ty::Bool,
                operand: ValueId::new(c),
            }),
            _ => None,
        };
        let Some(inst) = wrap else {
            return c;
        };
        let n = self.val();
        body.push(InstrNode::new(inst).with_result(ValueId::new(n)));
        sc.bools.push(n);
        n
    }

    fn op(&mut self, sc: &mut Scope, body: &mut Vec<InstrNode>) {
        let k = self.rng.below(100);
        if sc.ints.is_empty() || k < 10 {
            let ty = self.rng.pick(&TYS).clone();
            let v = self.konst(body, &ty);
            sc.ints.push((v, ty));
            return;
        }
        let (a, ty) = self.rng.pick(&sc.ints).clone();
        let r = self.val();
        let (operand, result) = (ValueId::new(a), ValueId::new(r));
        if k < 45 {
            let ops = [
                BinOp::Add,
                BinOp::Sub,
                BinOp::Mul,
                BinOp::And,
                BinOp::Or,
                BinOp::Xor,
                BinOp::UDiv,
                BinOp::URem,
                BinOp::SDiv,
                BinOp::SRem,
                BinOp::Shl,
                BinOp::LShr,
                BinOp::AShr,
                BinOp::RotL,
            ];
            let op = *self.rng.pick(&ops);
            let other = if matches!(op, BinOp::Shl | BinOp::LShr | BinOp::AShr) && self.rng.pct(60)
            {
                let amount = self.val();
                let raw = u128::from(self.rng.below(u64::from(self.bits(&ty)) + 2));
                let value = self.constant(&ty, raw);
                body.push(
                    InstrNode::new(Inst::Const {
                        ty: ty.clone(),
                        value,
                    })
                    .with_result(ValueId::new(amount)),
                );
                amount
            } else {
                self.of_ty(sc, body, &ty)
            };
            let (lhs, rhs) = if self.rng.pct(80) {
                (operand, ValueId::new(other))
            } else {
                (ValueId::new(other), operand)
            };
            body.push(
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: ty.clone(),
                    lhs,
                    rhs,
                })
                .with_result(result),
            );
            sc.ints.push((r, ty));
        } else if k < 52 {
            let ops = [UnOp::Not, UnOp::Neg, UnOp::CtPop, UnOp::CtLz, UnOp::CtTz];
            let op = *self.rng.pick(&ops);
            body.push(
                InstrNode::new(Inst::UnOp {
                    op,
                    ty: ty.clone(),
                    operand,
                })
                .with_result(result),
            );
            sc.ints.push((r, ty));
        } else if k < 67 {
            let to = self.rng.pick(&TYS).clone();
            let (from_bits, to_bits) = (self.bits(&ty), self.bits(&to));
            let op = if to_bits > from_bits {
                if self.rng.pct(50) {
                    CastOp::ZExt
                } else {
                    CastOp::SExt
                }
            } else if to_bits < from_bits {
                CastOp::Trunc
            } else {
                CastOp::Bitcast
            };
            body.push(
                InstrNode::new(Inst::Cast {
                    op,
                    src_ty: ty,
                    dst_ty: to.clone(),
                    operand,
                })
                .with_result(result),
            );
            sc.ints.push((r, to));
        } else if k < 77 {
            // `select`, often min/max shaped.
            let other = self.of_ty(sc, body, &ty);
            let c = self.val();
            let ops = [
                ICmpOp::Ult,
                ICmpOp::Ule,
                ICmpOp::Ugt,
                ICmpOp::Slt,
                ICmpOp::Sgt,
                ICmpOp::Eq,
                ICmpOp::Ne,
            ];
            let op = *self.rng.pick(&ops);
            body.push(
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: ty.clone(),
                    lhs: operand,
                    rhs: ValueId::new(other),
                })
                .with_result(ValueId::new(c)),
            );
            sc.bools.push(c);
            let (t, e) = if self.rng.pct(50) {
                (a, other)
            } else {
                (other, a)
            };
            let cond = if self.rng.pct(70) {
                c
            } else {
                self.cond(sc, body)
            };
            body.push(
                InstrNode::new(Inst::Select {
                    ty: ty.clone(),
                    cond: ValueId::new(cond),
                    then_val: ValueId::new(t),
                    else_val: ValueId::new(e),
                })
                .with_result(result),
            );
            sc.ints.push((r, ty));
        } else if k < 85 {
            let other = self.of_ty(sc, body, &ty);
            let flag = self.val();
            let ops = [
                OverflowOp::AddOverflow,
                OverflowOp::SubOverflow,
                OverflowOp::MulOverflow,
            ];
            let op = *self.rng.pick(&ops);
            body.push(
                InstrNode::new(Inst::Overflow {
                    op,
                    ty: ty.clone(),
                    lhs: operand,
                    rhs: ValueId::new(other),
                })
                .with_results([result, ValueId::new(flag)]),
            );
            sc.ints.push((r, ty));
            sc.bools.push(flag);
        } else if k < 90 {
            body.push(
                InstrNode::new(Inst::Copy {
                    ty: ty.clone(),
                    operand,
                })
                .with_result(result),
            );
            sc.ints.push((r, ty));
        } else {
            let c = self.cond(sc, body);
            let inst = if self.rng.pct(50) {
                Inst::Assume {
                    cond: ValueId::new(c),
                }
            } else {
                Inst::Assert {
                    cond: ValueId::new(c),
                    kind: AssertKind::Unspecified,
                    site: None,
                }
            };
            body.push(InstrNode::new(inst));
        }
    }

    fn ops(&mut self, sc: &mut Scope, body: &mut Vec<InstrNode>) {
        for _ in 0..self.rng.below(5) {
            self.op(sc, body);
        }
    }

    fn push(&mut self, id: u32, params: &[(u32, Ty)], body: Vec<InstrNode>) {
        let mut block = Block::new(BlockId::new(id));
        for (v, t) in params {
            block = block.with_param(ValueId::new(*v), t.clone());
        }
        block.body = body;
        self.lint_blocks.push(block.clone());
        self.oracle_blocks.push(block);
    }

    fn br(target: u32, args: Vec<ValueId>) -> InstrNode {
        InstrNode::new(Inst::Br {
            target: BlockId::new(target),
            args,
        })
    }

    /// Finish block `id` (its params, its body so far) and everything after it.
    fn region(
        &mut self,
        id: u32,
        params: Vec<(u32, Ty)>,
        mut body: Vec<InstrNode>,
        mut sc: Scope,
        depth: u32,
    ) {
        self.ops(&mut sc, &mut body);
        self.budget = self.budget.saturating_sub(1);
        let choice = if depth >= 4 || self.budget == 0 {
            0
        } else {
            self.rng.below(6)
        };
        match choice {
            0 => self.leaf(id, &params, body, sc),
            1 if depth > 0 => self.leaf(id, &params, body, sc),
            1 | 2 => {
                // A diamond joining at a block with one parameter.
                let c = self.cond(&mut sc, &mut body);
                let (t, e, j) = (self.blk(), self.blk(), self.blk());
                let jty = if sc.ints.is_empty() || self.rng.pct(20) {
                    self.rng.pick(&TYS).clone()
                } else {
                    self.rng.pick(&sc.ints).1.clone()
                };
                let mut tb = Vec::new();
                let mut tsc = sc.clone();
                self.ops(&mut tsc, &mut tb);
                let ta = self.of_ty(&tsc, &mut tb, &jty);
                tb.push(Self::br(j, vec![ValueId::new(ta)]));
                let mut eb = Vec::new();
                let mut esc = sc.clone();
                self.ops(&mut esc, &mut eb);
                let ea = self.of_ty(&esc, &mut eb, &jty);
                eb.push(Self::br(j, vec![ValueId::new(ea)]));
                // Sometimes an edge goes straight to the join, and sometimes
                // both do: two parallel edges into one block.
                let direct = self.rng.pct(30);
                let then_target = if direct { j } else { t };
                let then_args = if direct {
                    vec![ValueId::new(self.of_ty(&sc, &mut body, &jty))]
                } else {
                    vec![]
                };
                let both = direct && self.rng.pct(40);
                let (else_target, else_args) = if both {
                    (j, vec![ValueId::new(self.of_ty(&sc, &mut body, &jty))])
                } else {
                    (e, vec![])
                };
                body.push(InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(c),
                    then_target: BlockId::new(then_target),
                    then_args,
                    else_target: BlockId::new(else_target),
                    else_args,
                }));
                self.push(id, &params, body);
                if !direct {
                    self.push(t, &[], tb);
                }
                if !both {
                    self.push(e, &[], eb);
                }
                let p = self.val();
                let mut jsc = sc;
                jsc.ints.push((p, jty.clone()));
                self.region(j, vec![(p, jty)], Vec::new(), jsc, depth + 1);
            }
            3 => {
                // A diamond whose arms continue separately.
                let c = self.cond(&mut sc, &mut body);
                let (t, e) = (self.blk(), self.blk());
                body.push(InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(c),
                    then_target: BlockId::new(t),
                    then_args: vec![],
                    else_target: BlockId::new(e),
                    else_args: vec![],
                }));
                self.push(id, &params, body);
                self.region(t, vec![], Vec::new(), sc.clone(), depth + 1);
                self.region(e, vec![], Vec::new(), sc, depth + 1);
            }
            4 if sc.ints.is_empty() => self.leaf(id, &params, body, sc),
            4 => {
                let (v, ty) = self.rng.pick(&sc.ints).clone();
                let mut cases = Vec::new();
                let mut targets = Vec::new();
                let mut seen = Vec::new();
                for _ in 0..1 + self.rng.below(3) {
                    let raw = self.interesting(&ty);
                    if seen.contains(&raw) {
                        continue;
                    }
                    seen.push(raw);
                    let t = self.blk();
                    cases.push(SwitchCase {
                        value: self.constant(&ty, raw),
                        target: BlockId::new(t),
                        args: vec![],
                    });
                    targets.push(t);
                }
                let d = self.blk();
                body.push(InstrNode::new(Inst::Switch {
                    value: ValueId::new(v),
                    default: BlockId::new(d),
                    default_args: vec![],
                    cases,
                    exhaustive_enum_unreachable: false,
                }));
                self.push(id, &params, body);
                for t in targets {
                    self.region(t, vec![], Vec::new(), sc.clone(), depth + 1);
                }
                self.region(d, vec![], Vec::new(), sc, depth + 1);
            }
            _ => {
                // A loop: h(p) { if p <op> K { body: p' = p (+|*) step; br h(p') } else exit }.
                let ty = if sc.ints.is_empty() || self.rng.pct(30) {
                    self.rng.pick(&TYS).clone()
                } else {
                    self.rng.pick(&sc.ints).1.clone()
                };
                let init = self.of_ty(&sc, &mut body, &ty);
                let (h, lb, x) = (self.blk(), self.blk(), self.blk());
                body.push(Self::br(h, vec![ValueId::new(init)]));
                self.push(id, &params, body);
                let p = self.val();
                let mut hsc = sc.clone();
                hsc.ints.push((p, ty.clone()));
                let mut hb = Vec::new();
                let k = self.of_ty(&hsc, &mut hb, &ty);
                let c = self.val();
                let ops = [
                    ICmpOp::Ult,
                    ICmpOp::Ule,
                    ICmpOp::Slt,
                    ICmpOp::Ne,
                    ICmpOp::Ugt,
                ];
                let op = *self.rng.pick(&ops);
                hb.push(
                    InstrNode::new(Inst::ICmp {
                        op,
                        ty: ty.clone(),
                        lhs: ValueId::new(p),
                        rhs: ValueId::new(k),
                    })
                    .with_result(ValueId::new(c)),
                );
                hsc.bools.push(c);
                hb.push(InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(c),
                    then_target: BlockId::new(lb),
                    then_args: vec![],
                    else_target: BlockId::new(x),
                    else_args: vec![],
                }));
                self.push(h, &[(p, ty.clone())], hb);
                let mut bb = Vec::new();
                let mut bsc = hsc.clone();
                let step = self.of_ty(&bsc, &mut bb, &ty);
                let p2 = self.val();
                let step_op = if self.rng.pct(70) {
                    BinOp::Add
                } else {
                    BinOp::Mul
                };
                bb.push(
                    InstrNode::new(Inst::BinOp {
                        op: step_op,
                        ty: ty.clone(),
                        lhs: ValueId::new(p),
                        rhs: ValueId::new(step),
                    })
                    .with_result(ValueId::new(p2)),
                );
                bsc.ints.push((p2, ty));
                if self.rng.pct(30) {
                    // A site inside the loop body, behind its own branch.
                    let c2 = self.cond(&mut bsc, &mut bb);
                    let (leaf, back) = (self.blk(), self.blk());
                    bb.push(InstrNode::new(Inst::CondBr {
                        cond: ValueId::new(c2),
                        then_target: BlockId::new(leaf),
                        then_args: vec![],
                        else_target: BlockId::new(back),
                        else_args: vec![],
                    }));
                    self.push(lb, &[], bb);
                    self.leaf(leaf, &[], Vec::new(), bsc);
                    self.push(back, &[], vec![Self::br(h, vec![ValueId::new(p2)])]);
                } else {
                    bb.push(Self::br(h, vec![ValueId::new(p2)]));
                    self.push(lb, &[], bb);
                }
                self.region(x, vec![], Vec::new(), hsc, depth + 1);
            }
        }
    }

    /// A leaf: the lint twin allocates, the oracle twin returns the site and
    /// the count.
    fn leaf(&mut self, id: u32, params: &[(u32, Ty)], mut body: Vec<InstrNode>, mut sc: Scope) {
        if sc.ints.is_empty() {
            let v = self.konst(&mut body, &Ty::U64);
            sc.ints.push((v, Ty::U64));
        }
        let (count, count_ty) = self.rng.pick(&sc.ints).clone();
        // An element size whose line crossing sits near an interesting count.
        let limit = self.limit();
        let cap = umax(self.bits(&count_ty)).min(limit);
        let target = if self.rng.pct(15) {
            limit
        } else {
            (self.interesting(&count_ty) % cap).max(5)
        };
        let (elem_ty, elem) = match self.rng.below(10) {
            0 => (Ty::U64, 8),
            1 => (Ty::I128, 16),
            2 => self.struct_ty.clone(),
            _ => {
                let len = (limit / target).clamp(1, u128::from(u64::MAX));
                (Ty::Array(self.u8_ty, len as u64), len)
            }
        };
        let a = self.val();
        let mut lint_body = body.clone();
        lint_body.push(
            InstrNode::new(Inst::Alloca {
                ty: elem_ty,
                count: Some(ValueId::new(count)),
                align: None,
            })
            .with_result(ValueId::new(a)),
        );
        lint_body.push(InstrNode::new(Inst::Return { values: vec![] }));
        let site = self.val();
        let wide = self.val();
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(self.sites.len() as i128),
            })
            .with_result(ValueId::new(site)),
        );
        let op = if self.bits(&count_ty) == 128 {
            CastOp::Bitcast
        } else {
            CastOp::ZExt
        };
        body.push(
            InstrNode::new(Inst::Cast {
                op,
                src_ty: count_ty.clone(),
                dst_ty: Ty::U128,
                operand: ValueId::new(count),
            })
            .with_result(ValueId::new(wide)),
        );
        body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(site), ValueId::new(wide)],
        }));
        self.sites.push(Site {
            block: id,
            count_ty,
            elem,
        });
        let mut block = Block::new(BlockId::new(id));
        for (v, t) in params {
            block = block.with_param(ValueId::new(*v), t.clone());
        }
        let mut oracle = block.clone();
        block.body = lint_body;
        oracle.body = body;
        self.lint_blocks.push(block);
        self.oracle_blocks.push(oracle);
    }
}

fn target(triple: &str, pointer_bits: u32) -> TargetInfo {
    TargetInfo {
        triple: triple.into(),
        pointer_size: pointer_bits / 8,
        endianness: crate::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// One random program: (lint twin, oracle twin, sites, parameter types).
fn build(seed: u64, pointer_bits: u32) -> (Module, Module, Vec<Site>, Vec<Ty>) {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let params: Vec<Ty> = (0..1 + rng.below(3))
        .map(|_| rng.pick(&TYS).clone())
        .collect();
    let pivot = match rng.below(4) {
        0 => u128::from(rng.below(300)) + 5,
        1 => u128::from(rng.next() % 100_000) + 5,
        2 => u128::from(rng.next() | 5),
        _ => (1u128 << rng.below(63)) + 5,
    };
    let (canonical, _) = triples(pointer_bits);
    let mut lint = Module::new("lint");
    lint.target_info = Some(target(canonical, pointer_bits));
    let u8_ty = lint
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let struct_size = 24u64;
    let struct_id = lint.add_struct(StructDef {
        id: StructId::new(0),
        name: "Pair".into(),
        fields: Vec::new(),
        size: Some(struct_size),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    let mut g = Gen {
        rng,
        pointer_bits,
        next_val: 100,
        next_block: 0,
        lint_blocks: Vec::new(),
        oracle_blocks: Vec::new(),
        sites: Vec::new(),
        pivot,
        u8_ty,
        struct_ty: (Ty::Struct(struct_id), u128::from(struct_size)),
        budget: 12,
    };
    let entry: Vec<(u32, Ty)> = params
        .iter()
        .enumerate()
        .map(|(i, t)| (i as u32, t.clone()))
        .collect();
    let scope = Scope {
        ints: entry.clone(),
        bools: vec![],
    };
    g.region(0, entry, Vec::new(), scope, 0);
    let mut oracle = Module::new("oracle");
    oracle.target_info = lint.target_info.clone();
    let lint_ty = lint
        .add_func_type(FuncTy {
            abi: None,
            params: params.clone(),
            returns: vec![],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let oracle_ty = oracle
        .add_func_type(FuncTy {
            abi: None,
            params: params.clone(),
            returns: vec![Ty::U32, Ty::U128],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    // The entry first; the lint twin's other blocks shuffled.
    let mut blocks = g.lint_blocks;
    blocks.sort_by_key(|b| b.id.index() != 0);
    let mut shuffle = Rng(seed | 3);
    for i in (2..blocks.len()).rev() {
        let j = 1 + shuffle.below(i as u64) as usize;
        blocks.swap(i, j);
    }
    let mut f = Function::new(FuncId::new(0), "f", lint_ty, BlockId::new(0));
    f.blocks = blocks;
    lint.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    let mut oracle_blocks = g.oracle_blocks;
    oracle_blocks.sort_by_key(|b| b.id.index() != 0);
    let mut f = Function::new(FuncId::new(0), "f", oracle_ty, BlockId::new(0));
    f.blocks = oracle_blocks;
    oracle
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    (lint, oracle, g.sites, params)
}

/// (a canonical triple the interpreter runs, non-canonical triples of the
/// same pointer width).
fn triples(pointer_bits: u32) -> (&'static str, [&'static str; 2]) {
    if pointer_bits == 32 {
        (
            "wasm32-unknown-unknown",
            ["i686-unknown-linux-gnu", "armv7-unknown-linux-gnueabihf"],
        )
    } else {
        (
            "x86_64-unknown-linux-gnu",
            ["powerpc64le-unknown-linux-gnu", "s390x-unknown-linux-gnu"],
        )
    }
}

fn arg(rng: &mut Rng, ty: &Ty, pointer_bits: u32, pivot: u128) -> InterpretValue {
    let bits = ty.bit_width_with(pointer_bits).expect("an integer type");
    let m = umax(bits);
    let s = m >> 1;
    let pool = [
        0,
        1,
        2,
        5,
        255,
        256,
        1000,
        s,
        s + 1,
        m,
        m - 1,
        pivot & m,
        (pivot + 1) & m,
        pivot.wrapping_sub(1) & m,
        u128::from(rng.next()) & m,
        u128::from(rng.next()) << 64 | u128::from(rng.next()),
    ];
    let raw = *rng.pick(&pool) & m;
    InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::Int(
            InterpretInt::from_raw(bits, ty.is_signed(), raw).expect("an integer width"),
        ),
    }
}

/// The counts of what the run checked.
#[derive(Debug, Default)]
struct Tally {
    programs: u64,
    reached: u64,
    unreported: u64,
    /// Unreported executions whose bound came from the analysis: the count's
    /// type alone would cross the line.
    analysis_bounded: u64,
    /// Of those, the ones asking for more than half the line.
    near_the_line: u64,
    exceeds: u64,
}

fn run(start: u64, programs: u64, runs: u64, tally: &mut Tally, failures: &mut Vec<String>) {
    for seed in start..start + programs {
        let pointer_bits = if seed % 3 == 0 { 32 } else { 64 };
        let (lint, oracle, sites, params) = build(seed, pointer_bits);
        tally.programs += 1;
        let findings = check_allocation_bounds(&lint);
        // The same verdicts where the target has no alignment table.
        for triple in triples(pointer_bits).1 {
            let mut moved = lint.clone();
            moved.target_info = Some(target(triple, pointer_bits));
            let elsewhere = check_allocation_bounds(&moved);
            if elsewhere != findings && failures.len() < 20 {
                failures.push(format!(
                    "seed {seed}: verdicts differ on {triple}: {findings:?} vs {elsewhere:?}"
                ));
            }
        }
        let verdict = |block: u32| {
            findings
                .iter()
                .find(|f| f.block == block)
                .map(|f| (f.reason, f.count))
        };
        let limit = max_object_bytes(pointer_bits);
        let mut rng = Rng(seed ^ 0xDEAD_BEEF);
        let pivot = u128::from(rng.next());
        let interpreter = Interpreter::with_module(&oracle).with_options(InterpretOptions {
            fuel: 2_000,
            max_call_depth: 8,
            ..InterpretOptions::default()
        });
        for _ in 0..runs {
            let args: Vec<InterpretValue> = params
                .iter()
                .map(|t| arg(&mut rng, t, pointer_bits, pivot))
                .collect();
            let Ok(out) = interpreter.execute_func(FuncId::new(0), args.clone()) else {
                continue; // UB, a failed assert, or out of fuel: no site reached
            };
            let (InterpretValueKind::Int(site), InterpretValueKind::Int(raw)) =
                (&out.returns[0].kind, &out.returns[1].kind)
            else {
                panic!("the oracle returns (u32, u128): {out:?}");
            };
            let site = &sites[site.raw as usize];
            tally.reached += 1;
            let bits = site
                .count_ty
                .bit_width_with(pointer_bits)
                .expect("an integer");
            let raw = raw.raw & umax(bits);
            // The execution's count; zero, or a negative signed count, is UB.
            let count = if site.count_ty.is_signed() {
                let value = to_signed(raw, bits);
                (value > 0).then_some(value as u128)
            } else {
                (raw != 0).then_some(raw)
            };
            let Some(count) = count else {
                continue;
            };
            let bytes = count.checked_mul(site.elem);
            let fits = bytes.is_some_and(|b| b <= limit);
            match verdict(site.block) {
                None => {
                    tally.unreported += 1;
                    let type_max = if site.count_ty.is_signed() {
                        smax(bits)
                    } else {
                        umax(bits)
                    };
                    if type_max.checked_mul(site.elem).is_none_or(|b| b > limit) {
                        tally.analysis_bounded += 1;
                        if bytes.is_some_and(|b| b > limit / 2) {
                            tally.near_the_line += 1;
                        }
                    }
                    if !fits && failures.len() < 20 {
                        failures.push(format!(
                            "seed {seed}: bb{} not reported, but {count} x {} bytes exceeds \
                             the line; args {args:?}",
                            site.block, site.elem
                        ));
                    }
                }
                Some((AllocBoundReason::ExceedsObjectLimit, least)) => {
                    tally.exceeds += 1;
                    if (fits || count < least) && failures.len() < 20 {
                        failures.push(format!(
                            "seed {seed}: bb{} reported Exceeds (least {least}), but {count} \
                             x {} bytes fits or is below it; args {args:?}",
                            site.block, site.elem
                        ));
                    }
                }
                Some(_) => {}
            }
        }
    }
}

#[test]
fn the_analysis_agrees_with_interpreter_runs_of_random_programs() {
    let env = |name: &str| std::env::var(name).ok().and_then(|s| s.parse::<u64>().ok());
    let programs = env("TRUST_IR_ALLOC_BOUND_PROGRAMS").unwrap_or(1_500);
    let start = env("TRUST_IR_ALLOC_BOUND_SEED").unwrap_or(1);
    let mut tally = Tally::default();
    let mut failures = Vec::new();
    run(start, programs, 120, &mut tally, &mut failures);
    eprintln!("{tally:?}");
    assert!(failures.is_empty(), "{failures:#?}");
    // Non-vacuity: the run reached sites, checked unreported ones whose bound
    // only the analysis supplies, some of them near the line, and checked
    // reported-as-exceeding ones. (Measured 2026-09-30 over seeds 1..=1500:
    // 92626 reached, 3487 analysis-bounded, 437 near the line, 3039
    // exceeding; over 1..=6000: 363867, 17415, 1528, 12030. The floors are
    // about 60% of that, per program.)
    let per_program = |n: u64| n * tally.programs / 1_500;
    assert!(tally.reached >= per_program(55_000), "{tally:?}");
    assert!(tally.analysis_bounded >= per_program(2_000), "{tally:?}");
    assert!(tally.near_the_line >= per_program(250), "{tally:?}");
    assert!(tally.exceeds >= per_program(1_800), "{tally:?}");
}

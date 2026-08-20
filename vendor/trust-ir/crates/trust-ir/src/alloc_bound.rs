//! Static byte-budget check for stack/heap allocations — the
//! architecturally-correct home for byte-aware allocation bounds.
//!
//! UNLIKE the Rust/MIR layer (trust-vcgen), where `RawVec<T>` erases the element
//! type to `u8` and the trust-types `Ty` model drops `Vec<T>`'s `T` — so
//! `elem_size × count` cannot be recovered and the obligation can only bound the
//! element COUNT — the trust-ir `Alloca`/`HeapAlloc` carries the REAL element
//! `ty`. So here `elem_bytes × count` is EXACT: the same element COUNT yields a
//! different verdict for a 1-byte vs an 8-byte element, which is precisely the
//! byte-awareness the MIR layer cannot do.
//!
//! Two finding classes, both NON-FATAL by design (advisory; never a hard
//! `validate_module` error, so they can never reject valid IR — drop-in parity):
//!
//! * [`AllocBoundReason::ConstantOverBudget`] — a *provably-constant* byte size
//!   reaches [`ALLOC_BYTE_BUDGET`]. Byte-exact and high-confidence. The constant
//!   is recovered by folding integer arithmetic (`1 << 28`, `K * M`, masks,
//!   casts), so a size that is *computed* from constants is caught, not only a
//!   bare literal.
//!
//! * [`AllocBoundReason::UnboundedRuntimeCount`] — a *runtime* count with no
//!   provable upper bound: no dominating guard (`if n <= K`), no local mask/mod
//!   (`n & MASK`, `n % M`), and no narrowing cast bound it below the budget.
//!   This is the shape of the 2026-06-16 host OOM, where `vec![None; byte_len]`
//!   lowered to an allocation sized by a runtime `byte_len`. It is enforced at
//!   *runtime* by the interpreter memory budget
//!   (`crate::interpret::InterpretOptions::mem_budget`); statically we can only
//!   warn. The discharge analysis is SOUND in the conservative direction: we
//!   silence a count only when a real dominating guard or local definition
//!   proves it under budget, so a guard against a huge sentinel (e.g. the
//!   `usize::MAX` overflow check `usize::try_from` emits) does NOT silence it.
//!   When in doubt we flag — the safe direction for a hazard detector. The
//!   note fails OPEN on an unsized element type (cannot size it).

use std::collections::{HashMap, HashSet};

use crate::value::{BlockId, ValueId};
use crate::{BinOp, Block, CastOp, Constant, Function, ICmpOp, Inst, Module};

/// CFG analysis maps for a function: per-block predecessors and the dominator
/// set of each block. Computed lazily and only when a symbolic count appears.
type CfgMaps = (
    HashMap<BlockId, Vec<BlockId>>,
    HashMap<BlockId, HashSet<BlockId>>,
);

/// Per-allocation byte budget, mirroring the interpreter's default `mem_budget`
/// (256 MiB). A single allocation whose byte size reaches this is flagged.
pub const ALLOC_BYTE_BUDGET: u128 = 256 * 1024 * 1024;

/// Why an allocation was flagged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocBoundReason {
    /// Provably-constant byte size reaches the budget (byte-exact, high
    /// confidence). `count`/`bytes` carry the exact figures.
    ConstantOverBudget,
    /// Runtime count with no provable upper bound and no discharging guard,
    /// mask, or narrowing cast — advisory. The interpreter memory budget
    /// enforces this at runtime. `count`/`bytes` are `0` (unknown).
    UnboundedRuntimeCount,
}

/// One flagged allocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AllocBoundFinding {
    pub function: String,
    pub block: u32,
    /// `"alloca"` or `"heap_alloc"`.
    pub kind: &'static str,
    pub elem_ty: String,
    pub reason: AllocBoundReason,
    /// Exact element count for [`AllocBoundReason::ConstantOverBudget`], else `0`.
    pub count: u128,
    /// Exact byte size for [`AllocBoundReason::ConstantOverBudget`], else `0`.
    pub bytes: u128,
}

impl core::fmt::Display for AllocBoundFinding {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.reason {
            AllocBoundReason::ConstantOverBudget => write!(
                f,
                "{} of {} x {} (~{} bytes) in `{}` bb{} reaches the {}-byte allocation budget: \
                 bound the count or route it through a budget-checked allocator that fails closed",
                self.kind,
                self.count,
                self.elem_ty,
                self.bytes,
                self.function,
                self.block,
                ALLOC_BYTE_BUDGET
            ),
            AllocBoundReason::UnboundedRuntimeCount => write!(
                f,
                "{} of `{}` in `{}` bb{} is sized by a runtime count with no provable upper bound: \
                 bound it (e.g. `if n <= MAX`), mask it (`n & MASK`), or route it through a \
                 budget-checked allocator; enforced at runtime by the interpreter memory budget",
                self.kind, self.elem_ty, self.function, self.block
            ),
        }
    }
}

/// Scan `module` for allocations whose size reaches [`ALLOC_BYTE_BUDGET`]
/// (constant, byte-exact) or whose runtime count has no provable bound
/// (advisory). `pointer_bits` sizes pointer-width element types. The element
/// `ty` is not erased here, so the constant case is byte-exact.
pub fn check_allocation_bounds(module: &Module, pointer_bits: u32) -> Vec<AllocBoundFinding> {
    let mut findings = Vec::new();
    for func in &module.functions {
        let consts = const_eval(func);
        let defs = def_sites(func);
        // Dominator/predecessor maps are only needed if a symbolic count
        // appears; compute lazily on first use to keep constant-only functions
        // cheap.
        let mut cfg: Option<CfgMaps> = None;

        for block in &func.blocks {
            for node in &block.body {
                let (kind, ty, count) = match &node.inst {
                    Inst::Alloca { ty, count, .. } => ("alloca", ty, count),
                    Inst::HeapAlloc { ty, count, .. } => ("heap_alloc", ty, count),
                    _ => continue,
                };
                // `None` count is a single element ⇒ always bounded.
                let Some(cv) = count else { continue };
                // Unsized element type (struct/array/…) ⇒ cannot size; fail open.
                let Some(bits) = ty.bit_width_with(pointer_bits) else {
                    continue;
                };
                let elem_bytes = u128::from(bits) / 8;
                // Zero-sized element ⇒ allocation is empty regardless of count.
                if elem_bytes == 0 {
                    continue;
                }

                if let Some(&n) = consts.get(cv) {
                    // Constant count: byte-exact verdict. Non-positive count is a
                    // separate UB the interpreter already rejects; only flag a
                    // provably-large positive bound.
                    if n <= 0 {
                        continue;
                    }
                    let bytes = (n as u128).saturating_mul(elem_bytes);
                    if bytes >= ALLOC_BYTE_BUDGET {
                        findings.push(AllocBoundFinding {
                            function: func.name.clone(),
                            block: block.id.index(),
                            kind,
                            elem_ty: format!("{ty}"),
                            reason: AllocBoundReason::ConstantOverBudget,
                            count: n as u128,
                            bytes,
                        });
                    }
                    continue;
                }

                // Symbolic count: try to discharge it via a local definition
                // bound (mask/mod/narrowing cast) or a dominating guard. Only a
                // bound that proves it UNDER budget silences the note.
                let (preds, dom) = cfg.get_or_insert_with(|| {
                    let preds = predecessors(func);
                    let dom = dominators(func, &preds);
                    (preds, dom)
                });
                let local = local_count_bound(*cv, &defs, &consts, pointer_bits);
                let guard = guard_count_bound(func, block.id, *cv, &defs, &consts, dom, preds);
                let bound = match (local, guard) {
                    (Some(a), Some(b)) => Some(a.min(b)),
                    (Some(a), None) | (None, Some(a)) => Some(a),
                    (None, None) => None,
                };
                if let Some(b) = bound
                    && b.saturating_mul(elem_bytes) < ALLOC_BYTE_BUDGET
                {
                    continue; // discharged
                }
                findings.push(AllocBoundFinding {
                    function: func.name.clone(),
                    block: block.id.index(),
                    kind,
                    elem_ty: format!("{ty}"),
                    reason: AllocBoundReason::UnboundedRuntimeCount,
                    count: 0,
                    bytes: 0,
                });
            }
        }
    }
    findings
}

/// SSA constant evaluator: folds integer literals AND arithmetic over already-
/// known constants (`Add`/`Sub`/`Mul`/`Shl`/`And`/`Or`/`Xor`, `Copy`, integer
/// casts) to a fixpoint. Every fold is *checked* — an operation that would
/// overflow `i128` is not folded — so a recovered constant is EXACT and the
/// `ConstantOverBudget` verdict never false-positives. This recovers e.g.
/// `1 << 28` or `K * M` as the byte size, not just a bare literal.
fn const_eval(func: &Function) -> HashMap<ValueId, i128> {
    let mut m: HashMap<ValueId, i128> = HashMap::new();
    let mut changed = true;
    // Each pass can resolve at least one more value; bound the fixpoint by a
    // generous multiple of the instruction count as a non-termination backstop.
    let mut guard = 0usize;
    let limit = func.blocks.iter().map(|b| b.body.len()).sum::<usize>() + 4;
    while changed && guard < limit + 4 {
        changed = false;
        guard += 1;
        for block in &func.blocks {
            for node in &block.body {
                let Some(&res) = node.results.first() else {
                    continue;
                };
                if m.contains_key(&res) {
                    continue;
                }
                let folded = match &node.inst {
                    Inst::Const {
                        value: Constant::Int(n),
                        ..
                    } => Some(*n),
                    Inst::Copy { operand, .. } => m.get(operand).copied(),
                    Inst::Cast {
                        op,
                        src_ty,
                        dst_ty,
                        operand,
                    } => fold_cast(*op, src_ty, dst_ty, m.get(operand).copied()),
                    Inst::BinOp { op, lhs, rhs, .. } => {
                        fold_binop(*op, m.get(lhs).copied(), m.get(rhs).copied())
                    }
                    _ => None,
                };
                if let Some(v) = folded {
                    m.insert(res, v);
                    changed = true;
                }
            }
        }
    }
    m
}

/// Checked integer fold. Returns `None` (do not fold) on overflow or a
/// non-constant operand, keeping every recovered constant exact.
fn fold_binop(op: BinOp, lhs: Option<i128>, rhs: Option<i128>) -> Option<i128> {
    let (a, b) = (lhs?, rhs?);
    match op {
        BinOp::Add => a.checked_add(b),
        BinOp::Sub => a.checked_sub(b),
        BinOp::Mul => a.checked_mul(b),
        BinOp::And => Some(a & b),
        BinOp::Or => Some(a | b),
        BinOp::Xor => Some(a ^ b),
        BinOp::Shl => {
            // Fold via `a * 2^b` so value overflow is caught by `checked_mul`.
            if !(0..128).contains(&b) {
                return None;
            }
            1i128.checked_shl(b as u32).and_then(|m| a.checked_mul(m))
        }
        _ => None,
    }
}

/// Fold integer-preserving casts of a known constant. `ZExt`/`SExt`/`Bitcast`
/// preserve the integer value (zero-extension of a non-negative value, sign-
/// extension, and equal-width bitcast); `Trunc` masks to the destination width.
fn fold_cast(
    op: CastOp,
    _src_ty: &crate::ty::Ty,
    dst_ty: &crate::ty::Ty,
    val: Option<i128>,
) -> Option<i128> {
    let v = val?;
    match op {
        CastOp::SExt | CastOp::Bitcast => Some(v),
        CastOp::ZExt => (v >= 0).then_some(v),
        CastOp::Trunc => {
            let bits = dst_ty.bit_width_with(64)?;
            if bits == 0 || bits > 127 {
                return None;
            }
            let mask = (1i128 << bits) - 1;
            Some(v & mask)
        }
        _ => None,
    }
}

/// Maps each SSA value to its defining instruction (SSA: at most one).
fn def_sites(func: &Function) -> HashMap<ValueId, &Inst> {
    let mut m = HashMap::new();
    for block in &func.blocks {
        for node in &block.body {
            if let Some(&res) = node.results.first() {
                m.insert(res, &node.inst);
            }
        }
    }
    m
}

/// Largest unsigned value representable in `bits` bits.
fn type_max(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// Upper bound on a count established by HOW the count value is defined:
/// `n & MASK` ≤ `MASK`, `n % M` ≤ `M-1`, a narrowing/zero-extending cast bounds
/// it by the narrow type's range. `None` if the definition implies no bound.
fn local_count_bound(
    count: ValueId,
    defs: &HashMap<ValueId, &Inst>,
    consts: &HashMap<ValueId, i128>,
    pointer_bits: u32,
) -> Option<u128> {
    match defs.get(&count)? {
        Inst::BinOp {
            op: BinOp::And,
            lhs,
            rhs,
            ..
        } => {
            // `x & c ≤ c` for any non-negative mask `c`.
            for v in [lhs, rhs] {
                if let Some(&c) = consts.get(v)
                    && c >= 0
                {
                    return Some(c as u128);
                }
            }
            None
        }
        Inst::BinOp {
            op: BinOp::URem,
            rhs,
            ..
        } => {
            let &m = consts.get(rhs)?;
            (m >= 1).then(|| (m - 1) as u128)
        }
        Inst::BinOp {
            op: BinOp::SRem,
            rhs,
            ..
        } => {
            let &m = consts.get(rhs)?;
            (m != 0).then(|| m.unsigned_abs() - 1)
        }
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty,
            ..
        } => src_ty.bit_width_with(pointer_bits).map(type_max),
        Inst::Cast {
            op: CastOp::Trunc,
            dst_ty,
            ..
        } => dst_ty.bit_width_with(pointer_bits).map(type_max),
        _ => None,
    }
}

/// Tightest upper bound on `count` proven by a dominating guard. SOUND: a guard
/// edge bounds the allocation only when that edge's target dominates the alloc
/// block AND is that guard's sole successor-predecessor, so reaching the alloc
/// implies the comparison held. `None` if no guard bounds it.
fn guard_count_bound(
    func: &Function,
    alloc_block: BlockId,
    count: ValueId,
    defs: &HashMap<ValueId, &Inst>,
    consts: &HashMap<ValueId, i128>,
    dom: &HashMap<BlockId, HashSet<BlockId>>,
    preds: &HashMap<BlockId, Vec<BlockId>>,
) -> Option<u128> {
    let mut best: Option<u128> = None;
    for block in &func.blocks {
        for node in &block.body {
            let Inst::CondBr {
                cond,
                then_target,
                else_target,
                ..
            } = &node.inst
            else {
                continue;
            };
            let Some(Inst::ICmp { op, lhs, rhs, .. }) = defs.get(cond).copied() else {
                continue;
            };
            let (then_bound, else_bound) = if *lhs == count {
                edge_bounds(*op, consts.get(rhs).copied())
            } else if *rhs == count {
                // `K op count` is `count (swap op) K`.
                edge_bounds(swap_cmp(*op), consts.get(lhs).copied())
            } else {
                (None, None)
            };
            if let Some(b) = then_bound
                && dominates(*then_target, alloc_block, dom)
                && sole_pred(*then_target, block.id, preds)
            {
                best = Some(best.map_or(b, |x| x.min(b)));
            }
            if let Some(b) = else_bound
                && dominates(*else_target, alloc_block, dom)
                && sole_pred(*else_target, block.id, preds)
            {
                best = Some(best.map_or(b, |x| x.min(b)));
            }
        }
    }
    best
}

/// For `count <cmp> K`, the (then-edge, else-edge) upper bounds on `count`.
/// Signed and unsigned compares are treated alike for a non-negative `K` — a
/// negative count is a separate allocation UB, so for an upper bound the
/// distinction is immaterial. `None` means that edge implies no upper bound.
fn edge_bounds(op: ICmpOp, k: Option<i128>) -> (Option<u128>, Option<u128>) {
    let Some(k) = k else { return (None, None) };
    if k < 0 {
        return (None, None);
    }
    let k = k as u128;
    let km1 = k.saturating_sub(1);
    match op {
        // count < K : then count ≤ K-1 ; else count ≥ K (unbounded)
        ICmpOp::Ult | ICmpOp::Slt => (Some(km1), None),
        // count ≤ K : then K ; else unbounded
        ICmpOp::Ule | ICmpOp::Sle => (Some(k), None),
        // count > K : then unbounded ; else count ≤ K
        ICmpOp::Ugt | ICmpOp::Sgt => (None, Some(k)),
        // count ≥ K : then unbounded ; else count ≤ K-1
        ICmpOp::Uge | ICmpOp::Sge => (None, Some(km1)),
        // count == K : then exactly K ; else unbounded
        ICmpOp::Eq => (Some(k), None),
        ICmpOp::Ne => (None, Some(k)),
    }
}

/// The comparison `c` such that `K op count` ≡ `count c K` (operand swap).
fn swap_cmp(op: ICmpOp) -> ICmpOp {
    match op {
        ICmpOp::Ult => ICmpOp::Ugt,
        ICmpOp::Ule => ICmpOp::Uge,
        ICmpOp::Ugt => ICmpOp::Ult,
        ICmpOp::Uge => ICmpOp::Ule,
        ICmpOp::Slt => ICmpOp::Sgt,
        ICmpOp::Sle => ICmpOp::Sge,
        ICmpOp::Sgt => ICmpOp::Slt,
        ICmpOp::Sge => ICmpOp::Sle,
        ICmpOp::Eq => ICmpOp::Eq,
        ICmpOp::Ne => ICmpOp::Ne,
    }
}

/// `x` dominates `y` (every path from entry to `y` passes through `x`).
fn dominates(x: BlockId, y: BlockId, dom: &HashMap<BlockId, HashSet<BlockId>>) -> bool {
    dom.get(&y).is_some_and(|s| s.contains(&x))
}

/// `target`'s only predecessor is `guard` — so entering `target` is equivalent
/// to taking `guard`'s edge to it (the guard's comparison held).
fn sole_pred(target: BlockId, guard: BlockId, preds: &HashMap<BlockId, Vec<BlockId>>) -> bool {
    matches!(preds.get(&target), Some(ps) if ps.len() == 1 && ps[0] == guard)
}

/// Successor blocks reachable from `block`'s terminator(s).
fn successors(block: &Block) -> Vec<BlockId> {
    let mut out = Vec::new();
    for node in &block.body {
        match &node.inst {
            Inst::Br { target, .. } => out.push(*target),
            Inst::CondBr {
                then_target,
                else_target,
                ..
            } => {
                out.push(*then_target);
                out.push(*else_target);
            }
            Inst::Switch { default, cases, .. } => {
                out.push(*default);
                out.extend(cases.iter().map(|c| c.target));
            }
            Inst::Invoke {
                normal_dest,
                unwind_dest,
                ..
            } => {
                out.push(*normal_dest);
                out.push(*unwind_dest);
            }
            _ => {}
        }
    }
    out
}

fn predecessors(func: &Function) -> HashMap<BlockId, Vec<BlockId>> {
    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for block in &func.blocks {
        preds.entry(block.id).or_default();
    }
    for block in &func.blocks {
        for succ in successors(block) {
            preds.entry(succ).or_default().push(block.id);
        }
    }
    preds
}

/// Iterative dominator-set computation: `dom(b) = {b} ∪ ⋂ dom(p)` over `b`'s
/// predecessors, to a fixpoint. Unreachable blocks reduce to `{b}`.
fn dominators(
    func: &Function,
    preds: &HashMap<BlockId, Vec<BlockId>>,
) -> HashMap<BlockId, HashSet<BlockId>> {
    let all: HashSet<BlockId> = func.blocks.iter().map(|b| b.id).collect();
    let mut dom: HashMap<BlockId, HashSet<BlockId>> = HashMap::new();
    for block in &func.blocks {
        if block.id == func.entry {
            dom.insert(block.id, HashSet::from([block.id]));
        } else {
            dom.insert(block.id, all.clone());
        }
    }
    let mut changed = true;
    let mut guard = 0usize;
    let limit = func.blocks.len() * 2 + 4;
    while changed && guard < limit {
        changed = false;
        guard += 1;
        for block in &func.blocks {
            if block.id == func.entry {
                continue;
            }
            let mut new_set: Option<HashSet<BlockId>> = None;
            for p in preds.get(&block.id).into_iter().flatten() {
                let dp = &dom[p];
                new_set = Some(match new_set {
                    None => dp.clone(),
                    Some(acc) => acc.intersection(dp).copied().collect(),
                });
            }
            let mut new_set = new_set.unwrap_or_default();
            new_set.insert(block.id);
            if new_set != dom[&block.id] {
                dom.insert(block.id, new_set);
                changed = true;
            }
        }
    }
    dom
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::InstrNode;
    use crate::ty::Ty;
    use crate::value::{BlockId, FuncId, FuncTyId};
    use crate::{Block, Function};

    /// One function: `count_const`-element `Alloca` of `elem` (None ⇒ 1 element).
    fn module_with(count_const: Option<i128>, elem: Ty) -> Module {
        let mut module = Module::new("alloc-bound-test");
        let mut func = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        let count_val = count_const.map(|n| {
            let v = ValueId::new(0);
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(n),
                })
                .with_result(v),
            );
            v
        });
        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: elem,
                count: count_val,
                align: None,
            })
            .with_result(ValueId::new(1)),
        );
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn flags_constant_alloc_over_byte_budget() {
        // 2^26 × i64 = 512 MiB ≥ 256 MiB ⇒ flagged, byte-exact.
        let m = module_with(Some(1 << 26), Ty::I64);
        let f = check_allocation_bounds(&m, 64);
        assert_eq!(f.len(), 1, "a 512 MiB constant alloca must be flagged");
        assert_eq!(f[0].kind, "alloca");
        assert_eq!(f[0].reason, AllocBoundReason::ConstantOverBudget);
        assert_eq!(f[0].bytes, (1u128 << 26) * 8);
    }

    #[test]
    fn byte_aware_same_count_small_element_not_flagged() {
        // SAME element COUNT as above, but i8 elements: 2^26 × 1 = 64 MiB < 256 MiB
        // ⇒ NOT flagged. This element-SIZE sensitivity is exactly what the MIR
        // layer cannot do (RawVec<T> erases T to u8).
        let m = module_with(Some(1 << 26), Ty::I8);
        assert!(check_allocation_bounds(&m, 64).is_empty());
    }

    #[test]
    fn single_element_alloca_is_bounded() {
        assert!(check_allocation_bounds(&module_with(None, Ty::I64), 64).is_empty());
    }

    /// Build a single-block function whose alloca count is `count_inst`'s result,
    /// preceded by `setup` instructions. Returns the module.
    fn module_one_block(setup: Vec<InstrNode>, count: ValueId, elem: Ty) -> Module {
        let mut module = Module::new("m");
        let mut func = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body.extend(setup);
        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: elem,
                count: Some(count),
                align: None,
            })
            .with_result(ValueId::new(100)),
        );
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn computed_constant_over_budget_is_folded_and_flagged() {
        // count = 1 << 28 (folded through Shl), i8 elements ⇒ 256 MiB ≥ budget.
        let one = ValueId::new(0);
        let sh = ValueId::new(1);
        let twenty_eight = ValueId::new(2);
        let setup = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            })
            .with_result(one),
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(28),
            })
            .with_result(twenty_eight),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Shl,
                ty: Ty::U64,
                lhs: one,
                rhs: twenty_eight,
            })
            .with_result(sh),
        ];
        let m = module_one_block(setup, sh, Ty::I8);
        let f = check_allocation_bounds(&m, 64);
        assert_eq!(
            f.len(),
            1,
            "a computed-constant 256 MiB alloca must be flagged"
        );
        assert_eq!(f[0].reason, AllocBoundReason::ConstantOverBudget);
        assert_eq!(f[0].bytes, 1u128 << 28);
    }

    #[test]
    fn bare_symbolic_count_flagged_as_unbounded_note() {
        // A runtime count with no definition, guard, or mask in scope is the
        // crash shape ⇒ advisory note (was previously silent).
        let mut m = Module::new("sym");
        let mut func = Function::new(FuncId::new(0), "g", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block = block.with_param(ValueId::new(7), Ty::U64);
        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(ValueId::new(7)),
                align: None,
            })
            .with_result(ValueId::new(1)),
        );
        func.blocks.push(block);
        m.add_function(func);
        let f = check_allocation_bounds(&m, 64);
        assert_eq!(
            f.len(),
            1,
            "an unbounded runtime count must be flagged as a note"
        );
        assert_eq!(f[0].reason, AllocBoundReason::UnboundedRuntimeCount);
    }

    #[test]
    fn masked_symbolic_count_not_flagged() {
        // count = n & 0xFFFF ⇒ ≤ 65535; × i64 = 512 KiB < budget ⇒ discharged.
        let n = ValueId::new(7); // block param (runtime)
        let mask = ValueId::new(0);
        let masked = ValueId::new(1);
        let setup = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(0xFFFF),
            })
            .with_result(mask),
            InstrNode::new(Inst::BinOp {
                op: BinOp::And,
                ty: Ty::U64,
                lhs: n,
                rhs: mask,
            })
            .with_result(masked),
        ];
        let m = module_one_block(setup, masked, Ty::I64);
        assert!(
            check_allocation_bounds(&m, 64).is_empty(),
            "a masked count must be discharged, not flagged"
        );
    }

    #[test]
    fn mod_symbolic_count_not_flagged() {
        // count = n % 1024 ⇒ ≤ 1023 ⇒ discharged.
        let n = ValueId::new(7);
        let m_const = ValueId::new(0);
        let rem = ValueId::new(1);
        let setup = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1024),
            })
            .with_result(m_const),
            InstrNode::new(Inst::BinOp {
                op: BinOp::URem,
                ty: Ty::U64,
                lhs: n,
                rhs: m_const,
            })
            .with_result(rem),
        ];
        let m = module_one_block(setup, rem, Ty::I64);
        assert!(check_allocation_bounds(&m, 64).is_empty());
    }

    #[test]
    fn narrowing_cast_count_not_flagged() {
        // count = zext(u16) ⇒ ≤ 65535 ⇒ discharged even for i64 elements.
        let n16 = ValueId::new(7);
        let widened = ValueId::new(1);
        let setup = vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U16,
                dst_ty: Ty::U64,
                operand: n16,
            })
            .with_result(widened),
        ];
        let m = module_one_block(setup, widened, Ty::I64);
        assert!(check_allocation_bounds(&m, 64).is_empty());
    }

    /// Two-block function: bb0 does `if count <cmp> K` and branches to bb1 (the
    /// alloca, sole-pred bb0) on the true edge, else returns. Models a guard.
    fn module_guarded(op: ICmpOp, k: i128, elem: Ty) -> Module {
        let mut module = Module::new("guarded");
        let mut func = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));

        let count = ValueId::new(7); // entry block param (runtime)
        let kv = ValueId::new(0);
        let cond = ValueId::new(1);
        let mut bb0 = Block::new(BlockId::new(0)).with_param(count, Ty::U64);
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(k),
            })
            .with_result(kv),
        );
        bb0.body.push(
            InstrNode::new(Inst::ICmp {
                op,
                ty: Ty::U64,
                lhs: count,
                rhs: kv,
            })
            .with_result(cond),
        );
        bb0.body.push(InstrNode::new(Inst::CondBr {
            cond,
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }));

        let mut bb1 = Block::new(BlockId::new(1));
        bb1.body.push(
            InstrNode::new(Inst::Alloca {
                ty: elem,
                count: Some(count),
                align: None,
            })
            .with_result(ValueId::new(2)),
        );
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));

        let mut bb2 = Block::new(BlockId::new(2));
        bb2.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));

        func.blocks.extend([bb0, bb1, bb2]);
        module.add_function(func);
        module
    }

    #[test]
    fn dominating_guard_below_budget_not_flagged() {
        // if count < 1000 { alloca i64[count] } ⇒ ≤ 999 × 8 < budget ⇒ silent.
        let m = module_guarded(ICmpOp::Ult, 1000, Ty::I64);
        assert!(
            check_allocation_bounds(&m, 64).is_empty(),
            "a count guarded below budget must not be flagged"
        );
    }

    #[test]
    fn dominating_guard_against_huge_sentinel_still_flagged() {
        // if count < usize::MAX { alloca i64[count] }: the guard is the overflow
        // check `usize::try_from` emits — K × 8 ≫ budget ⇒ NOT discharged. This
        // is the exact false-discharge the crude "compared ⇒ bounded" heuristic
        // would have gotten wrong, letting the crash through.
        let m = module_guarded(ICmpOp::Ult, i128::from(u64::MAX), Ty::I64);
        let f = check_allocation_bounds(&m, 64);
        assert_eq!(
            f.len(),
            1,
            "a guard against a huge sentinel must not discharge"
        );
        assert_eq!(f[0].reason, AllocBoundReason::UnboundedRuntimeCount);
    }
}

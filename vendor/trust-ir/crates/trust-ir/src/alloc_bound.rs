//! Allocation-size bounds: which `Alloca` / `HeapAlloc` sizes the program does
//! NOT provably bound.
//!
//! # The question, and the one line it is judged against
//!
//! An allocation of `count` elements of `ty` asks for `count × size_of(ty)`
//! bytes. This lint proves an upper bound on that size and reports the
//! allocation when the proof does not keep it within the largest object the
//! target can hold: `isize::MAX` bytes at the module's pointer width
//! ([`max_object_bytes`]). That line is the target's definition of an object —
//! Rust's `Layout`, LLVM's object model and every GEP offset are bounded by it
//! — and not a budget: it has no knob, it is the same for every program on a
//! target, and a bound above it proves nothing, because the count's own
//! integer type is always such a bound. There is NO availability threshold:
//! the 256 MiB `ALLOC_BYTE_BUDGET` this module used to judge against was
//! deleted, approved by the owner 2026-09-29 ("delete the 256 MiB number; the
//! lint reports only allocations whose size is not provably bounded"). The
//! superproject's `trust-vcgen` carries its own copy of that number
//! (`UNBOUNDED_ALLOC_BYTE_CEILING`, `generate/mod.rs`); it is not a trust-ir
//! artifact and follows in a later superproject change.
//!
//! The element type is not erased here (unlike MIR's `RawVec<T>`, which is
//! `u8`-typed), so the byte size is exact: the same count is bounded for a
//! 1-byte element and not for an 8-byte one.
//!
//! Three finding classes, all NON-FATAL (advisory, never a `validate_module`
//! error, so they can never reject valid IR):
//!
//! * [`AllocBoundReason::ExceedsObjectLimit`] — every execution that reaches
//!   the allocation asks for more than the largest object: it can never
//!   succeed. Byte-exact for a constant count.
//! * [`AllocBoundReason::UnboundedRuntimeCount`] — no bound the analysis proves
//!   keeps the size within the largest object: the size is decided by a
//!   runtime value the program never checked. This is the shape of the
//!   2026-06-16 host OOM, where `vec![None; byte_len]` lowered to an allocation
//!   sized by an unchecked runtime `byte_len`. (The reference interpreter's
//!   allocations are sparse since v50, so a huge `Alloca` costs the host
//!   O(1); this lint is about the compiled program.)
//! * [`AllocBoundReason::UnknownElementSize`] — the element type has no byte
//!   size (a sequence, set, record, closure, dialect or error type; a missing
//!   or cyclic type entry; a struct with no declared size; an enum with no
//!   layout the target answers for): nothing bounds the size, so it is
//!   reported, never skipped.
//!
//! # Element sizes
//!
//! A SIZE needs no alignment, so elements are sized on every target, inside or
//! outside the canonical scalar-ALIGNMENT table [`Module::ty_layout_shape`]
//! keys on: a scalar by its width (`bool` one byte, `isize`/`usize`, pointers
//! and handles one pointer word, a fat pointer two), a struct by its declared
//! `size`, a tuple by its layout descriptor's, an array or vector by its
//! element's size times its length, a refinement by its base, an enum by its
//! layout descriptor's size or else the canonical layout
//! ([`Module::enum_layout_shape`], whose tag and payload placement needs the
//! target's alignments, so outside that table such an enum is unsized). Where
//! the layout authority answers, these are its sizes (a test holds them
//! equal). Sizes are `u128` products, so an element of `2^61` bytes or more is
//! judged exactly, and a product beyond `u128` exceeds every object.
//!
//! # What "provably bounded" covers
//!
//! The analysis judges the executions the IR DEFINES. A zero count, and a
//! signed count at or below zero, is undefined behaviour at the allocation in
//! the reference interpreter, so it has no size to bound: an unchecked `i64`
//! count of bytes is not reported — its defined values are at most
//! `i64::MAX`, within a 64-bit target's line — although compiled code that
//! sign-extends a negative count would ask for about `2^64` bytes. Undefined
//! counts are a UB question, not a size question. And because the line is the
//! largest object, not an availability figure, a count narrower than the
//! pointer width is bounded by its type: `u32` elements of `u64` (at most 32
//! GiB) are within a 64-bit target's line and are not reported. Silence on
//! either is therefore not a statement that the allocation is small.
//!
//! # The analysis
//!
//! Every integer SSA value gets an unsigned interval — and, where a signed
//! comparison supplies one, an upper bound on its signed reading — computed
//! ONCE, where the value is defined:
//!
//! * constants, and exact interval arithmetic (`Add`/`Sub`/`Mul` only while
//!   the result provably does not wrap, or exactly when both operands are
//!   constants; masks, shifts, division, remainder, `zext`/`sext`/`trunc`), so
//!   `1 << 28`, `n & 0xFFFF`, `n % 1024` and `n as u16 as usize` are bounded;
//! * `Select` joins its arms, each refined by its condition, so
//!   `n.min(K)` — `select(n < K, n, K)` — is bounded by `K`;
//! * a block parameter joins the arguments of its incoming edges, each refined
//!   by that edge's branch condition; an edge not walked yet (a loop's back
//!   edge) contributes an unbounded argument, so a loop-carried count is
//!   reported, which is the sound direction;
//! * a branch condition (`ICmp`, through `Copy` and boolean negation — its
//!   one spelling `bxor %c, true` (SPEC_RATIFICATIONS §3.2), the overloaded
//!   `xor` with a constant, and the refused `not bool` alike — including
//!   the flag of an unsigned `Overflow`: its false edge makes the result the
//!   exact, unwrapped value), a `Switch` case, an `Assume` and an `Assert`
//!   refine the compared values throughout the region they dominate. A
//!   signed comparison bounds a signed reading only: `(n as i64) < K` does not
//!   bound an unsigned `n`, whose values above `i64::MAX` pass it.
//!
//! Each transfer function (`binop`, `unop`, `cast`, `cmp_facts`,
//! `switch_default`, `unwrapped`, `Range::meet` / `Range::join`) is
//! checked against the reference interpreter's own integer arithmetic,
//! exhaustively at small widths (`alloc_bound_property_tests.rs`), and the
//! whole analysis against interpreter runs of random programs
//! (`alloc_bound_differential_tests.rs`).
//!
//! # Cost
//!
//! One walk of the dominator tree visits each block once, children in reverse
//! postorder, which finishes every forward-edge predecessor of a block before
//! the block; facts are scoped to the walk (pushed on entry, undone on exit).
//! Time and memory are O(blocks + edges + instructions + branch arguments) per
//! function — a census counts that work and the tests hold it to the
//! program's own counts — plus element sizing, which is memoized per type-table
//! entry, struct and enum, so it is O(types + structs + enums + tuple
//! descriptors) per module however the types nest. Two costs come from shared
//! analyses this lint calls and are theirs, not this walk's: the shared
//! [`DominatorTree`] (a Cooper–Harvey–Kennedy fixpoint over ordered maps,
//! super-linear in the worst case: measured about 26× time per 10× blocks at
//! 10^6 blocks, 2026-09-30), and, once per descriptor-less enum element type,
//! [`Module::enum_layout_shape`], which lays out the enum's fields without
//! memoization. There is no fixpoint, no iteration limit and no size refusal
//! here. A fact refines the values defined in the region it dominates, and
//! the count itself where it is used; a value computed BEFORE a guard on its
//! operand keeps its unguarded range, so such an allocation is reported (a
//! false positive, never a false discharge). Unreachable blocks never
//! allocate and are not judged. A function whose CFG the dominator analysis
//! rejects is judged block by block with no branch facts, which only reports
//! more.

use std::collections::HashMap;

use crate::analysis::DominatorTree;
use crate::shape::PointerLayoutShape;
use crate::ty::{EnumDef, Ty};
use crate::value::{BlockId, EnumId, StructId, TyId, ValueId};
use crate::{BinOp, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Module, OverflowOp, UnOp};

/// The largest object, in bytes, a target with `pointer_bits`-bit pointers can
/// hold: `isize::MAX` at that width (`2^(pointer_bits - 1) - 1`). Every
/// allocation must fit it to exist; it is the target's definition, not a
/// tunable figure. Above 128 bits the line is beyond `u128` and this
/// saturates (the validator admits pointer sizes of 1, 2, 4 and 8 bytes).
pub fn max_object_bytes(pointer_bits: u32) -> u128 {
    match pointer_bits {
        0 => 0,
        1..=128 => u128::MAX.checked_shr(129 - pointer_bits).unwrap_or(0),
        _ => u128::MAX,
    }
}

/// Why an allocation was reported.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocBoundReason {
    /// Every execution reaching the allocation asks for more bytes than the
    /// target's largest object: it can never succeed. `count` / `bytes` are
    /// the LEAST such request (exact for a constant count).
    ExceedsObjectLimit,
    /// No bound the analysis proves keeps the size within the target's largest
    /// object. `count` / `bytes` are `0` (not known).
    UnboundedRuntimeCount,
    /// The element type has no byte size (see the module docs), so no bound
    /// on the allocation's size exists. `count` / `bytes` are `0`.
    UnknownElementSize,
}

/// One reported allocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AllocBoundFinding {
    pub function: String,
    pub block: u32,
    /// `"alloca"` or `"heap_alloc"`.
    pub kind: &'static str,
    pub elem_ty: String,
    pub reason: AllocBoundReason,
    /// The least element count, for [`AllocBoundReason::ExceedsObjectLimit`];
    /// else `0`.
    pub count: u128,
    /// The least byte size (saturating), for
    /// [`AllocBoundReason::ExceedsObjectLimit`]; else `0`.
    pub bytes: u128,
    /// The target's largest object in bytes ([`max_object_bytes`] at the
    /// module's pointer width): the line the size was judged against.
    pub object_limit: u128,
}

impl core::fmt::Display for AllocBoundFinding {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.reason {
            AllocBoundReason::ExceedsObjectLimit => write!(
                f,
                "{} of {} x {} ({} bytes) in `{}` bb{} exceeds the largest object the target \
                 can hold ({} bytes): it can never succeed",
                self.kind,
                self.count,
                self.elem_ty,
                self.bytes,
                self.function,
                self.block,
                self.object_limit
            ),
            AllocBoundReason::UnboundedRuntimeCount => write!(
                f,
                "{} of `{}` in `{}` bb{}: no bound proves its size within the target's \
                 {}-byte object limit; bound the count (`if n <= MAX`), mask it (`n & MASK`) \
                 or narrow it (advisory)",
                self.kind, self.elem_ty, self.function, self.block, self.object_limit
            ),
            AllocBoundReason::UnknownElementSize => write!(
                f,
                "{} of `{}` in `{}` bb{}: the element type has no byte size, so nothing \
                 proves the allocation within the target's {}-byte object limit (advisory)",
                self.kind, self.elem_ty, self.function, self.block, self.object_limit
            ),
        }
    }
}

/// Report every `Alloca` / `HeapAlloc` of `module` whose byte size is not
/// provably within the largest object of the module's target
/// ([`Module::pointer_bits`]), in function, block and instruction order.
pub fn check_allocation_bounds(module: &Module) -> Vec<AllocBoundFinding> {
    check(module).0
}

/// The work one [`check_allocation_bounds`] run did, counted where it is done:
/// the tests hold each count to the program's own size, so a fixpoint, a
/// repeated walk or an unmemoized type recursion fails a test instead of only
/// running long.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct Census {
    /// Blocks evaluated (a block of a well-formed CFG once, when reachable).
    blocks: usize,
    /// Instructions evaluated.
    nodes: usize,
    /// Successor edges whose argument ranges were recorded.
    edges_recorded: usize,
    /// Incoming-edge arguments read while joining block parameters.
    arguments_joined: usize,
    /// Element-size computations that missed the memo: each distinct element
    /// type, type-table entry, struct and enum at most once.
    sizes_computed: usize,
}

/// [`check_allocation_bounds`] and the work it did.
fn check(module: &Module) -> (Vec<AllocBoundFinding>, Census) {
    let pointer_bits = module.pointer_bits();
    let object_limit = max_object_bytes(pointer_bits);
    let mut sizer = Sizer::new(module);
    let mut census = Census::default();
    let mut findings = Vec::new();
    for func in &module.functions {
        let mut walk = Walk {
            module,
            func,
            pointer_bits,
            object_limit,
            sizer: &mut sizer,
            census: &mut census,
            def: HashMap::new(),
            active: HashMap::new(),
            undo: Vec::new(),
            conds: HashMap::new(),
            bool_consts: HashMap::new(),
            edge_args: HashMap::new(),
            found: Vec::new(),
        };
        walk.run();
        let mut found = walk.found;
        found.sort_by_key(|(position, _)| *position);
        findings.extend(found.into_iter().map(|(_, finding)| finding));
    }
    census.sizes_computed = sizer.computed;
    (findings, census)
}

// ---------------------------------------------------------------------------
// Element sizes.

/// A byte size: exact, beyond `u128`, or not determinable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Bytes {
    Exact(u128),
    /// More than `u128::MAX` bytes: beyond every object up to a 128-bit target.
    Beyond,
    Unknown,
}

impl Bytes {
    /// `n` of these. An unknown size stays unknown (the layout authority
    /// refuses `[T; 0]` of an unlayoutable `T` too).
    fn times(self, n: u128) -> Self {
        match self {
            Bytes::Exact(bytes) => bytes.checked_mul(n).map_or(Bytes::Beyond, Bytes::Exact),
            Bytes::Beyond if n == 0 => Bytes::Exact(0),
            Bytes::Beyond => Bytes::Beyond,
            Bytes::Unknown => Bytes::Unknown,
        }
    }
}

/// One type-table entry's size, or the mark of one being sized (a cycle).
#[derive(Debug, Clone, Copy)]
enum Slot {
    Sizing,
    Sized(Bytes),
}

/// Element byte sizes for one module, memoized per type, type-table entry and
/// enum (see the module docs for the rules).
struct Sizer<'m> {
    module: &'m Module,
    pointer_bytes: u128,
    /// Each struct's declared size, the first definition of an id winning, as
    /// in the layout authority.
    structs: HashMap<StructId, Option<u64>>,
    enums: HashMap<EnumId, &'m EnumDef>,
    /// Each tuple type's descriptor sizes (more than one is incoherent).
    tuples: HashMap<&'m Ty, Vec<u64>>,
    by_ty: HashMap<Ty, Bytes>,
    by_id: HashMap<TyId, Slot>,
    by_enum: HashMap<EnumId, Bytes>,
    /// The layout authority, one table for the module, so each enum's
    /// canonical layout lays out what it reaches once for every enum asked.
    layouts: crate::LayoutTable<'m>,
    /// Memo misses ([`Census::sizes_computed`]).
    computed: usize,
}

impl<'m> Sizer<'m> {
    fn new(module: &'m Module) -> Self {
        let mut structs = HashMap::new();
        for def in &module.structs {
            structs.entry(def.id).or_insert(def.size);
        }
        let mut enums = HashMap::new();
        for def in &module.enums {
            enums.entry(def.id).or_insert(def);
        }
        let mut tuples: HashMap<&Ty, Vec<u64>> = HashMap::new();
        for desc in &module.tuple_layouts {
            if let Some(ty @ Ty::Tuple(_)) = module.types.get(desc.tuple_type.as_usize()) {
                tuples.entry(ty).or_default().push(desc.size);
            }
        }
        Self {
            module,
            pointer_bytes: u128::from(module.pointer_bits()) / 8,
            structs,
            enums,
            tuples,
            by_ty: HashMap::new(),
            by_id: HashMap::new(),
            by_enum: HashMap::new(),
            layouts: module.layout_table(),
            computed: 0,
        }
    }

    /// The byte size of one `ty`.
    fn bytes(&mut self, ty: &Ty) -> Bytes {
        if let Some(bytes) = self.by_ty.get(ty) {
            return *bytes;
        }
        self.computed += 1;
        let bytes = self.compute(ty);
        self.by_ty.insert(ty.clone(), bytes);
        bytes
    }

    /// The byte size of type-table entry `id`; a cycle has none. A chain of
    /// entries (`[ty.k-1; n]`, a refinement of `ty.k-1`, …) is followed in a
    /// loop, not by recursion, so its length costs heap, never stack.
    fn entry(&mut self, id: TyId) -> Bytes {
        // The entries entered on the way down, each with its multiplier.
        let mut chain: Vec<(TyId, u128)> = Vec::new();
        let mut current = id;
        let mut bytes = loop {
            match self.by_id.get(&current) {
                Some(Slot::Sized(bytes)) => break *bytes,
                Some(Slot::Sizing) => break Bytes::Unknown, // a cycle
                None => {}
            }
            let Some(ty) = self.module.types.get(current.as_usize()) else {
                break Bytes::Unknown;
            };
            self.computed += 1;
            self.by_id.insert(current, Slot::Sizing);
            match ty {
                Ty::Array(elem, len) => {
                    chain.push((current, u128::from(*len)));
                    current = *elem;
                }
                Ty::Refine(base, _) => {
                    chain.push((current, 1));
                    current = *base;
                }
                other => {
                    let bytes = self.compute(other);
                    self.by_id.insert(current, Slot::Sized(bytes));
                    break bytes;
                }
            }
        };
        for (entry, factor) in chain.into_iter().rev() {
            bytes = bytes.times(factor);
            self.by_id.insert(entry, Slot::Sized(bytes));
        }
        bytes
    }

    fn enum_bytes(&mut self, id: EnumId) -> Bytes {
        if let Some(bytes) = self.by_enum.get(&id) {
            return *bytes;
        }
        self.computed += 1;
        let bytes = match self.enums.get(&id) {
            None => Bytes::Unknown,
            Some(def) => match &def.layout {
                // A producer descriptor's size is normative.
                Some(desc) => Bytes::Exact(u128::from(desc.size)),
                // The canonical layout places the tag and payload by the
                // target's alignments; only the layout authority knows them.
                None => self
                    .layouts
                    .enum_layout(id)
                    .ok()
                    .filter(|layout| layout.size_bits.is_multiple_of(8))
                    .map_or(Bytes::Unknown, |layout| {
                        Bytes::Exact(u128::from(layout.size_bits / 8))
                    }),
            },
        };
        self.by_enum.insert(id, bytes);
        bytes
    }

    fn compute(&mut self, ty: &Ty) -> Bytes {
        let word = Bytes::Exact(self.pointer_bytes);
        match ty {
            Ty::Storage(layout) => {
                if layout.is_well_formed(self.module.pointer_bits()) {
                    Bytes::Exact(u128::from(layout.size_bytes))
                } else {
                    Bytes::Unknown
                }
            }
            Ty::Bool | Ty::I8 | Ty::U8 => Bytes::Exact(1),
            Ty::I16 | Ty::U16 | Ty::F16 => Bytes::Exact(2),
            Ty::I32 | Ty::U32 | Ty::F32 | Ty::Char => Bytes::Exact(4),
            Ty::I64 | Ty::U64 | Ty::F64 => Bytes::Exact(8),
            Ty::I128 | Ty::U128 => Bytes::Exact(16),
            Ty::Isize
            | Ty::Usize
            | Ty::Handle(_)
            | Ty::Ptr
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Func(_) => word,
            Ty::FatPtr(kind) => {
                let pointer_bits = self.module.pointer_bits();
                PointerLayoutShape::fat(pointer_bits, kind.metadata_shape())
                    .total_bits()
                    .map_or(Bytes::Beyond, |bits| Bytes::Exact(u128::from(bits) / 8))
            }
            Ty::Unit | Ty::Never => Bytes::Exact(0),
            Ty::Struct(id) => self
                .structs
                .get(id)
                .copied()
                .flatten()
                .map_or(Bytes::Unknown, |size| Bytes::Exact(u128::from(size))),
            Ty::Array(elem, len) => self.entry(*elem).times(u128::from(*len)),
            Ty::Vector(elem, lanes) => self.bytes(elem).times(u128::from(*lanes)),
            Ty::Refine(base, _) => self.entry(*base),
            Ty::Enum(id) => self.enum_bytes(*id),
            Ty::Tuple(elems) if elems.is_empty() => Bytes::Exact(0),
            Ty::Tuple(_) => match self.tuples.get(ty).map(Vec::as_slice) {
                // A declared tuple layout needs a target, as the authority says.
                Some([size]) if self.module.target_info.is_some() => {
                    Bytes::Exact(u128::from(*size))
                }
                _ => Bytes::Unknown,
            },
            Ty::Error
            | Ty::Dialect(_)
            | Ty::Closure(_)
            | Ty::Set(..)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Tensor(..) => Bytes::Unknown,
            Ty::Ext(e) => e.unreachable(),
        }
    }
}

// ---------------------------------------------------------------------------
// The value domain.

/// All-ones at `bits` (1..=128).
fn umax(bits: u32) -> u128 {
    u128::MAX >> (128 - bits)
}

/// The largest non-negative signed value at `bits`, as an unsigned number.
fn smax(bits: u32) -> u128 {
    umax(bits) >> 1
}

/// The signed reading of the low `bits` bits of `v`.
fn to_signed(v: u128, bits: u32) -> i128 {
    let shift = 128 - bits;
    ((v << shift) as i128) >> shift
}

/// The two's-complement bits of `s` at `bits`.
fn to_unsigned(s: i128, bits: u32) -> u128 {
    (s as u128) & umax(bits)
}

/// The smallest signed value at `bits`.
fn smin(bits: u32) -> i128 {
    to_signed(smax(bits) + 1, bits)
}

/// The smallest all-ones number at or above `v` (`0` for `0`).
fn ones_covering(v: u128) -> u128 {
    if v == 0 {
        0
    } else {
        u128::MAX >> v.leading_zeros()
    }
}

/// What is known about one integer value of `bits` bits: its unsigned reading
/// lies in `lo..=hi` (`lo > hi`: no execution reaches here), and its signed
/// reading is at most `shi` when that is tighter than the interval says.
/// `signed` is the declared type's reading, used only where the count is
/// judged (a signed count must be positive).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Range {
    bits: u32,
    signed: bool,
    lo: u128,
    hi: u128,
    shi: Option<i128>,
}

impl Range {
    fn top(bits: u32, signed: bool) -> Self {
        Self {
            bits,
            signed,
            lo: 0,
            hi: umax(bits),
            shi: None,
        }
    }

    fn exact(bits: u32, signed: bool, v: u128) -> Self {
        let v = v & umax(bits);
        Self {
            bits,
            signed,
            lo: v,
            hi: v,
            shi: None,
        }
    }

    fn empty(bits: u32, signed: bool) -> Self {
        Self {
            bits,
            signed,
            lo: 1,
            hi: 0,
            shi: None,
        }
    }

    fn span(bits: u32, signed: bool, lo: u128, hi: u128) -> Self {
        Self {
            bits,
            signed,
            lo,
            hi,
            shi: None,
        }
    }

    fn is_empty(&self) -> bool {
        self.lo > self.hi
    }

    fn exact_value(&self) -> Option<u128> {
        (self.lo == self.hi).then_some(self.lo)
    }

    /// Every value is non-negative in its signed reading.
    fn nonneg(&self) -> bool {
        self.hi <= smax(self.bits)
    }

    /// An upper bound on the signed reading.
    fn signed_hi(&self) -> i128 {
        let from_bits = if self.lo > smax(self.bits) {
            to_signed(self.hi, self.bits)
        } else {
            self.hi.min(smax(self.bits)) as i128
        };
        self.shi.map_or(from_bits, |s| s.min(from_bits))
    }

    /// Fold `shi` into the interval where it says something about the bits,
    /// and drop it where the interval already says as much.
    fn normalize(mut self) -> Self {
        if self.is_empty() {
            return Self::empty(self.bits, self.signed);
        }
        let Some(s) = self.shi else {
            return self;
        };
        if s < smin(self.bits) {
            return Self::empty(self.bits, self.signed);
        }
        if s < 0 {
            // A negative signed reading: the bits lie above `smax`.
            self.lo = self.lo.max(smax(self.bits) + 1);
            self.hi = self.hi.min(to_unsigned(s, self.bits));
        } else if self.nonneg() {
            self.hi = self.hi.min(s as u128);
        }
        if self.is_empty() {
            return Self::empty(self.bits, self.signed);
        }
        self.shi = None;
        if s < self.signed_hi() {
            self.shi = Some(s);
        }
        self
    }

    /// Both hold (intersection). `self`'s declared reading is kept.
    fn meet(self, other: Self) -> Self {
        if self.bits != other.bits {
            return self;
        }
        Self {
            bits: self.bits,
            signed: self.signed,
            lo: self.lo.max(other.lo),
            hi: self.hi.min(other.hi),
            shi: match (self.shi, other.shi) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, None) => a,
                (None, b) => b,
            },
        }
        .normalize()
    }

    /// Either holds (hull). `self`'s declared reading is kept.
    fn join(self, other: Self) -> Self {
        if self.bits != other.bits {
            return Self::top(self.bits, self.signed);
        }
        if self.is_empty() {
            return Self {
                signed: self.signed,
                ..other
            };
        }
        if other.is_empty() {
            return self;
        }
        Self {
            bits: self.bits,
            signed: self.signed,
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
            shi: Some(self.signed_hi().max(other.signed_hi())),
        }
        .normalize()
    }

    fn at_most(bits: u32, hi: Option<u128>) -> Self {
        match hi {
            Some(hi) => Self::span(bits, false, 0, hi.min(umax(bits))),
            None => Self::empty(bits, false),
        }
    }

    fn at_least(bits: u32, lo: Option<u128>) -> Self {
        match lo {
            Some(lo) if lo <= umax(bits) => Self::span(bits, false, lo, umax(bits)),
            _ => Self::empty(bits, false),
        }
    }

    fn signed_at_most(bits: u32, shi: Option<i128>) -> Self {
        match shi {
            Some(s) => Self {
                shi: Some(s),
                ..Self::top(bits, false)
            }
            .normalize(),
            None => Self::empty(bits, false),
        }
    }
}

/// `a op b` at `bits` over the interpreter's integer semantics (wrapping
/// `Add`/`Sub`/`Mul`; a zero divisor or an out-of-range shift is undefined
/// behaviour, so no execution continues with one).
fn binop(op: BinOp, bits: u32, signed: bool, a: Range, b: Range) -> Range {
    let top = Range::top(bits, signed);
    if a.bits != bits || b.bits != bits {
        return top;
    }
    if a.is_empty() || b.is_empty() {
        return Range::empty(bits, signed);
    }
    let max = umax(bits);
    let exact = |v: u128| Range::exact(bits, signed, v);
    let both = a.exact_value().zip(b.exact_value());
    let span = |lo: u128, hi: u128| Range::span(bits, signed, lo, hi);
    match op {
        BinOp::Add => match (a.lo.checked_add(b.lo), a.hi.checked_add(b.hi)) {
            (Some(lo), Some(hi)) if hi <= max => span(lo, hi),
            _ => both.map_or(top, |(x, y)| exact(x.wrapping_add(y))),
        },
        BinOp::Sub => {
            if a.lo >= b.hi {
                span(a.lo - b.hi, a.hi - b.lo)
            } else {
                both.map_or(top, |(x, y)| exact(x.wrapping_sub(y)))
            }
        }
        BinOp::Mul => match a.hi.checked_mul(b.hi) {
            Some(hi) if hi <= max => span(a.lo * b.lo, hi),
            _ => both.map_or(top, |(x, y)| exact(x.wrapping_mul(y))),
        },
        BinOp::And => both.map_or(span(0, a.hi.min(b.hi)), |(x, y)| exact(x & y)),
        BinOp::Or => both.map_or(
            span(a.lo.max(b.lo), ones_covering(a.hi.max(b.hi))),
            |(x, y)| exact(x | y),
        ),
        BinOp::Xor => both.map_or(span(0, ones_covering(a.hi.max(b.hi))), |(x, y)| {
            exact(x ^ y)
        }),
        BinOp::UDiv => {
            // A zero divisor is UB: every continuing execution has `b >= 1`.
            if b.hi == 0 {
                return Range::empty(bits, signed);
            }
            span(a.lo / b.hi, a.hi / b.lo.max(1))
        }
        BinOp::URem => {
            if b.hi == 0 {
                return Range::empty(bits, signed);
            }
            match both {
                Some((x, y)) if y != 0 => exact(x % y),
                _ => span(0, a.hi.min(b.hi - 1)),
            }
        }
        // On non-negative operands the signed forms are the unsigned ones.
        BinOp::SDiv if a.nonneg() && b.nonneg() => binop(BinOp::UDiv, bits, signed, a, b),
        BinOp::SRem if a.nonneg() && b.nonneg() => binop(BinOp::URem, bits, signed, a, b),
        BinOp::Shl | BinOp::LShr | BinOp::AShr => {
            // An amount at or above the width is UB.
            let width = u128::from(bits);
            if b.lo >= width {
                return Range::empty(bits, signed);
            }
            let (min_shift, max_shift) = (b.lo as u32, b.hi.min(width - 1) as u32);
            match op {
                BinOp::Shl if a.hi <= max >> max_shift => {
                    span(a.lo << min_shift, a.hi << max_shift)
                }
                BinOp::Shl => both.map_or(top, |(x, y)| exact(x << y)),
                BinOp::LShr => span(a.lo >> max_shift, a.hi >> min_shift),
                _ if a.nonneg() => span(a.lo >> max_shift, a.hi >> min_shift),
                _ => both.map_or(top, |(x, y)| {
                    exact(to_unsigned(to_signed(x, bits) >> y, bits))
                }),
            }
        }
        _ => top,
    }
}

/// `op` on an integer operand.
fn unop(op: UnOp, bits: u32, signed: bool, a: Range) -> Range {
    if a.bits != bits {
        return Range::top(bits, signed);
    }
    if a.is_empty() {
        return Range::empty(bits, signed);
    }
    let max = umax(bits);
    match op {
        UnOp::Not => Range::span(bits, signed, max - a.hi, max - a.lo),
        UnOp::Neg => a.exact_value().map_or(Range::top(bits, signed), |x| {
            Range::exact(bits, signed, 0u128.wrapping_sub(x))
        }),
        UnOp::CtPop | UnOp::CtLz | UnOp::CtTz => Range::span(bits, signed, 0, u128::from(bits)),
        _ => Range::top(bits, signed),
    }
}

/// An integer-to-integer cast of `a` (`from` bits) to `to` bits.
fn cast(op: CastOp, to: u32, signed: bool, from: u32, a: Range) -> Range {
    if a.bits != from {
        return Range::top(to, signed);
    }
    if a.is_empty() {
        return Range::empty(to, signed);
    }
    let keep = || Range::span(to, signed, a.lo, a.hi);
    match op {
        CastOp::ZExt if to >= from => keep(),
        CastOp::SExt if to >= from => {
            if a.nonneg() {
                keep()
            } else if a.lo > smax(from) {
                // Every value is negative: sign extension adds the same high bits.
                let high = umax(to) - umax(from);
                Range::span(to, signed, a.lo + high, a.hi + high)
            } else {
                Range::top(to, signed)
            }
        }
        CastOp::Trunc if to <= from => {
            if a.hi <= umax(to) {
                keep()
            } else {
                a.exact_value()
                    .map_or(Range::top(to, signed), |x| Range::exact(to, signed, x))
            }
        }
        CastOp::Bitcast if to == from => Range {
            signed,
            shi: None,
            ..a
        },
        _ => Range::top(to, signed),
    }
}

/// What `x op y` holding implies for each operand, `[for x, for y]`: the
/// facts to meet into their current ranges `x` and `y` (`None`: nothing).
fn cmp_facts(op: ICmpOp, bits: u32, x: Range, y: Range) -> [Option<Range>; 2] {
    // `a < b` (`strict`) or `a <= b`, unsigned: [for a, for b].
    let unsigned_lt = |strict: bool, a: Range, b: Range| {
        let (hi, lo) = if strict {
            (b.hi.checked_sub(1), a.lo.checked_add(1))
        } else {
            (Some(b.hi), Some(a.lo))
        };
        [
            Some(Range::at_most(bits, hi)),
            Some(Range::at_least(bits, lo)),
        ]
    };
    // The same order on the signed readings.
    let signed_lt = |strict: bool, a: Range, b: Range| {
        let bound = if strict {
            b.signed_hi().checked_sub(1)
        } else {
            Some(b.signed_hi())
        };
        let small = Range::signed_at_most(bits, bound);
        if a.nonneg() && b.nonneg() {
            // Both non-negative: the signed order is the unsigned one.
            let [for_a, for_b] = unsigned_lt(strict, a, b);
            [for_a.map(|fact| fact.meet(small)), for_b]
        } else {
            [Some(small), None]
        }
    };
    let swap = |[a, b]: [Option<Range>; 2]| [b, a];
    // `r != c` for an exact `c` at an end of `r` trims that end.
    let ne = |r: Range, other: Range| {
        let c = other.exact_value()?;
        if r.lo == c {
            Some(Range::at_least(bits, c.checked_add(1)))
        } else if r.hi == c {
            Some(Range::at_most(bits, c.checked_sub(1)))
        } else {
            None
        }
    };
    let same = |r: Range| {
        Range {
            signed: false,
            shi: Some(r.signed_hi()),
            ..r
        }
        .normalize()
    };
    match op {
        ICmpOp::Ult => unsigned_lt(true, x, y),
        ICmpOp::Ule => unsigned_lt(false, x, y),
        ICmpOp::Ugt => swap(unsigned_lt(true, y, x)),
        ICmpOp::Uge => swap(unsigned_lt(false, y, x)),
        ICmpOp::Slt => signed_lt(true, x, y),
        ICmpOp::Sle => signed_lt(false, x, y),
        ICmpOp::Sgt => swap(signed_lt(true, y, x)),
        ICmpOp::Sge => swap(signed_lt(false, y, x)),
        ICmpOp::Eq => [Some(same(y)), Some(same(x))],
        ICmpOp::Ne => [ne(x, y), ne(y, x)],
    }
}

/// The selector `r` on a `Switch`'s default edge: it is none of `cases` (its
/// bits at `r`'s width), which trims the ends of its interval.
fn switch_default(r: Range, mut cases: Vec<u128>) -> Range {
    if r.is_empty() {
        return Range::empty(r.bits, false);
    }
    cases.sort_unstable();
    let (mut lo, mut hi) = (r.lo, r.hi);
    for &c in &cases {
        if c == lo {
            let Some(next) = lo.checked_add(1) else {
                return Range::empty(r.bits, false);
            };
            lo = next;
        }
    }
    for &c in cases.iter().rev() {
        if c == hi {
            let Some(next) = hi.checked_sub(1) else {
                return Range::empty(r.bits, false);
            };
            hi = next;
        }
    }
    Range::span(r.bits, false, lo, hi)
}

/// The result of an UNSIGNED `op` on `a` and `b` where its overflow flag is
/// false: the exact, unwrapped value.
fn unwrapped(op: OverflowOp, bits: u32, a: Range, b: Range) -> Range {
    if a.is_empty() || b.is_empty() {
        return Range::empty(bits, false);
    }
    let max = umax(bits);
    match op {
        OverflowOp::AddOverflow => Range::span(
            bits,
            false,
            a.lo.saturating_add(b.lo),
            a.hi.saturating_add(b.hi).min(max),
        ),
        // No overflow means `a >= b`.
        OverflowOp::SubOverflow => match a.hi.checked_sub(b.lo) {
            Some(hi) => Range::span(bits, false, a.lo.saturating_sub(b.hi), hi),
            None => Range::empty(bits, false),
        },
        OverflowOp::MulOverflow => Range::span(
            bits,
            false,
            a.lo.saturating_mul(b.lo),
            a.hi.saturating_mul(b.hi).min(max),
        ),
    }
}

/// The negation of a comparison.
fn negate(op: ICmpOp) -> ICmpOp {
    match op {
        ICmpOp::Eq => ICmpOp::Ne,
        ICmpOp::Ne => ICmpOp::Eq,
        ICmpOp::Ult => ICmpOp::Uge,
        ICmpOp::Uge => ICmpOp::Ult,
        ICmpOp::Ule => ICmpOp::Ugt,
        ICmpOp::Ugt => ICmpOp::Ule,
        ICmpOp::Slt => ICmpOp::Sge,
        ICmpOp::Sge => ICmpOp::Slt,
        ICmpOp::Sle => ICmpOp::Sgt,
        ICmpOp::Sgt => ICmpOp::Sle,
    }
}

/// A boolean value's meaning, when it is one the analysis reads.
#[derive(Debug, Clone, Copy)]
enum Atom {
    /// `lhs op rhs` over `bits`-bit integers.
    Cmp {
        op: ICmpOp,
        bits: u32,
        lhs: ValueId,
        rhs: ValueId,
    },
    /// The overflow flag of an UNSIGNED `Overflow`: when it is false the
    /// result is the exact, unwrapped value, which lies in `exact`.
    Overflowed { result: ValueId, exact: Range },
}

/// `atom`, or its negation when `negated`.
#[derive(Debug, Clone, Copy)]
struct Cond {
    atom: Atom,
    negated: bool,
}

/// A position in source order: (block index in the function, instruction).
type Position = (usize, usize);

/// One function's walk.
struct Walk<'m, 's> {
    module: &'m Module,
    func: &'m Function,
    pointer_bits: u32,
    object_limit: u128,
    /// Element byte sizes, shared across functions.
    sizer: &'s mut Sizer<'m>,
    census: &'s mut Census,
    /// Each integer value's range where it is defined.
    def: HashMap<ValueId, Range>,
    /// Refinements by the facts in scope; `undo` restores them on scope exit.
    active: HashMap<ValueId, Range>,
    undo: Vec<(ValueId, Option<Range>)>,
    /// Boolean values the analysis reads as a condition.
    conds: HashMap<ValueId, Cond>,
    /// The `Bool` constants, so `bxor %c, true` reads as the negation of `%c`.
    bool_consts: HashMap<ValueId, bool>,
    /// Argument ranges each walked edge passes, by (source block, successor).
    edge_args: HashMap<(BlockId, usize), Vec<Option<Range>>>,
    found: Vec<(Position, AllocBoundFinding)>,
}

/// The successor edges of a terminator in the canonical order
/// [`DominatorTree::edge_dominates`] numbers them: `Br` 0; `CondBr` then/else
/// 0/1; `Switch` cases, then default; an invoke-family terminator
/// normal/unwind 0/1.
fn successors(inst: &Inst) -> Vec<(BlockId, &[ValueId])> {
    // The exhaustive accessor (amendment D §1.3), whose order is this one.
    inst.successor_edges()
        .into_iter()
        .map(|edge| (edge.target, edge.args))
        .collect()
}

impl Walk<'_, '_> {
    fn int_bits(&self, ty: &Ty) -> Option<u32> {
        if !ty.is_integer() {
            return None;
        }
        ty.bit_width_with(self.pointer_bits)
            .filter(|bits| (1..=128).contains(bits))
    }

    fn cur(&self, v: ValueId) -> Option<Range> {
        self.active.get(&v).or_else(|| self.def.get(&v)).copied()
    }

    fn cur_or_top(&self, v: ValueId, bits: u32) -> Range {
        self.cur(v)
            .filter(|r| r.bits == bits)
            .unwrap_or(Range::top(bits, false))
    }

    /// Record that `v` lies in `fact` for the rest of the current scope.
    fn refine(&mut self, v: ValueId, fact: Range) {
        let old = self.active.get(&v).copied();
        let base = self.cur(v).unwrap_or(Range::top(fact.bits, false));
        let new = base.meet(fact);
        if new != base {
            self.undo.push((v, old));
            self.active.insert(v, new);
        }
    }

    fn undo_to(&mut self, mark: usize) {
        while self.undo.len() > mark {
            let (v, old) = self.undo.pop().expect("above the mark");
            match old {
                Some(range) => self.active.insert(v, range),
                None => self.active.remove(&v),
            };
        }
    }

    /// The ranges `lhs op rhs` holding implies, one per operand.
    fn cmp_facts(
        &self,
        op: ICmpOp,
        bits: u32,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Vec<(ValueId, Range)> {
        let x = self.cur_or_top(lhs, bits);
        let y = self.cur_or_top(rhs, bits);
        let [for_lhs, for_rhs] = cmp_facts(op, bits, x, y);
        [(lhs, for_lhs), (rhs, for_rhs)]
            .into_iter()
            .filter_map(|(v, fact)| Some((v, fact?)))
            .collect()
    }

    /// What `cond` being `truth` implies.
    fn facts(&self, cond: ValueId, truth: bool) -> Vec<(ValueId, Range)> {
        let Some(Cond { atom, negated }) = self.conds.get(&cond).copied() else {
            return Vec::new();
        };
        let holds = truth != negated;
        match atom {
            Atom::Cmp { op, bits, lhs, rhs } => {
                self.cmp_facts(if holds { op } else { negate(op) }, bits, lhs, rhs)
            }
            Atom::Overflowed { result, exact } if !holds => vec![(result, exact)],
            Atom::Overflowed { .. } => Vec::new(),
        }
    }

    fn assume(&mut self, cond: ValueId, truth: bool) {
        for (v, fact) in self.facts(cond, truth) {
            self.refine(v, fact);
        }
    }

    /// `v`'s range where `cond` is `truth`.
    fn under(&self, v: ValueId, bits: u32, cond: ValueId, truth: bool) -> Range {
        let base = self.cur_or_top(v, bits);
        self.facts(cond, truth)
            .into_iter()
            .filter(|(subject, _)| *subject == v)
            .fold(base, |r, (_, fact)| r.meet(fact))
    }

    /// The facts taking successor `index` of `terminator` implies.
    fn edge_facts(&self, terminator: &Inst, index: usize) -> Vec<(ValueId, Range)> {
        match terminator {
            Inst::CondBr { cond, .. } => self.facts(*cond, index == 0),
            Inst::Switch { value, cases, .. } => {
                let Some(r) = self.cur(*value) else {
                    return Vec::new();
                };
                let case_bits = |c: &Constant| match c {
                    Constant::Int(i) => Some(*i as u128 & umax(r.bits)),
                    Constant::U128(u) => Some(*u & umax(r.bits)),
                    _ => None,
                };
                if let Some(case) = cases.get(index) {
                    return case_bits(&case.value)
                        .map(|c| vec![(*value, Range::exact(r.bits, false, c))])
                        .unwrap_or_default();
                }
                // The default edge: the selector is none of the cases.
                let excluded = cases
                    .iter()
                    .filter_map(|case| case_bits(&case.value))
                    .collect();
                vec![(*value, switch_default(r, excluded))]
            }
            _ => Vec::new(),
        }
    }

    /// Whether `bytes` is more than the largest object. Beyond `u128` it is,
    /// unless the line itself is (a pointer wider than 128 bits).
    fn over_limit(&self, bytes: Bytes) -> bool {
        match bytes {
            Bytes::Exact(bytes) => bytes > self.object_limit,
            Bytes::Beyond => self.pointer_bits <= 128,
            Bytes::Unknown => false,
        }
    }

    /// Whether `bytes` is provably within the largest object.
    fn within_limit(&self, bytes: Bytes) -> bool {
        match bytes {
            Bytes::Exact(bytes) => bytes <= self.object_limit,
            Bytes::Beyond | Bytes::Unknown => false,
        }
    }

    /// Judge one allocation against the object limit.
    fn judge(&mut self, at: Position, kind: &'static str, ty: &Ty, count: Option<ValueId>) {
        // (least count of an execution that allocates, proven upper bound)
        let (least, most) = match count {
            None => (1, Some(1)),
            Some(count) => match self.cur(count) {
                None => (1, None),
                Some(r) if r.is_empty() => return, // unreachable
                Some(r) if r.signed => {
                    // A signed count must be positive; zero or negative is UB.
                    let top = r.signed_hi();
                    if top < 1 || r.lo > smax(r.bits) {
                        return;
                    }
                    (r.lo.max(1), Some(r.hi.min(top as u128)))
                }
                Some(r) => {
                    if r.hi == 0 {
                        return; // a zero count is UB
                    }
                    (r.lo.max(1), Some(r.hi))
                }
            },
        };
        let elem = self.sizer.bytes(ty);
        let least_bytes = elem.times(least);
        let reason = if elem == Bytes::Exact(0) {
            return; // nothing is allocated, whatever the count
        } else if elem == Bytes::Unknown {
            AllocBoundReason::UnknownElementSize
        } else if self.over_limit(least_bytes) {
            AllocBoundReason::ExceedsObjectLimit
        } else if !most.is_some_and(|most| self.within_limit(elem.times(most))) {
            AllocBoundReason::UnboundedRuntimeCount
        } else {
            return;
        };
        let exceeds = reason == AllocBoundReason::ExceedsObjectLimit;
        self.found.push((
            at,
            AllocBoundFinding {
                function: self.func.name.clone(),
                block: self.func.blocks[at.0].id.index(),
                kind,
                elem_ty: format!("{ty}"),
                reason,
                count: if exceeds { least } else { 0 },
                bytes: match least_bytes {
                    Bytes::Exact(bytes) if exceeds => bytes,
                    _ if exceeds => u128::MAX,
                    _ => 0,
                },
                object_limit: self.object_limit,
            },
        ));
    }

    /// Give `node`'s integer results their ranges (and read its conditions),
    /// with the facts now in scope.
    fn eval(&mut self, at: Position, node: &InstrNode) {
        self.census.nodes += 1;
        let first = node.results.first().copied();
        match &node.inst {
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(b),
            } => {
                if let Some(r) = first {
                    self.bool_consts.insert(r, *b);
                }
            }
            Inst::Const { ty, value } => {
                if let (Some(bits), Some(r)) = (self.int_bits(ty), first) {
                    let range = match value {
                        Constant::Int(i) => Range::exact(bits, ty.is_signed(), *i as u128),
                        Constant::U128(u) => Range::exact(bits, ty.is_signed(), *u),
                        _ => Range::top(bits, ty.is_signed()),
                    };
                    self.def.insert(r, range);
                }
            }
            Inst::Copy { ty, operand } => {
                if let Some(r) = first {
                    if let Some(bits) = self.int_bits(ty) {
                        let range = Range {
                            signed: ty.is_signed(),
                            ..self.cur_or_top(*operand, bits)
                        };
                        self.def.insert(r, range);
                    }
                    if let Some(cond) = self.conds.get(operand).copied() {
                        self.conds.insert(r, cond);
                    }
                }
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                if let (Some(to), Some(r)) = (self.int_bits(dst_ty), first) {
                    let range = match self.int_bits(src_ty) {
                        Some(from) => cast(
                            *op,
                            to,
                            dst_ty.is_signed(),
                            from,
                            self.cur_or_top(*operand, from),
                        ),
                        None => Range::top(to, dst_ty.is_signed()),
                    };
                    self.def.insert(r, range);
                }
            }
            // Boolean negation's one spelling, `bxor %c, true`
            // (SPEC_RATIFICATIONS §3.2): an exclusive-or of a condition with a
            // `Bool` constant is that condition, negated when the constant is
            // `true`. The overloaded `xor bool` computes the same value.
            Inst::BinOp {
                op: BinOp::BXor | BinOp::Xor,
                ty: Ty::Bool,
                lhs,
                rhs,
            } => {
                let operands = [(*lhs, *rhs), (*rhs, *lhs)];
                let read = operands.iter().find_map(|(c, k)| {
                    let cond = self.conds.get(c).copied()?;
                    let flip = self.bool_consts.get(k).copied()?;
                    Some(Cond {
                        negated: cond.negated != flip,
                        ..cond
                    })
                });
                if let (Some(cond), Some(r)) = (read, first) {
                    self.conds.insert(r, cond);
                }
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                if let (Some(bits), Some(r)) = (self.int_bits(ty), first) {
                    let (a, b) = (self.cur_or_top(*lhs, bits), self.cur_or_top(*rhs, bits));
                    self.def.insert(r, binop(*op, bits, ty.is_signed(), a, b));
                }
            }
            Inst::UnOp { op, ty, operand } => {
                if let Some(r) = first {
                    if matches!(ty, Ty::Bool) && *op == UnOp::Not {
                        if let Some(cond) = self.conds.get(operand).copied() {
                            self.conds.insert(
                                r,
                                Cond {
                                    negated: !cond.negated,
                                    ..cond
                                },
                            );
                        }
                    } else if let Some(bits) = self.int_bits(ty) {
                        let a = self.cur_or_top(*operand, bits);
                        self.def.insert(r, unop(*op, bits, ty.is_signed(), a));
                    }
                }
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                if let (Some(bits), Some(r)) = (self.int_bits(ty), first) {
                    let then_range = self.under(*then_val, bits, *cond, true);
                    let else_range = self.under(*else_val, bits, *cond, false);
                    let range = Range {
                        signed: ty.is_signed(),
                        ..then_range.join(else_range)
                    };
                    self.def.insert(r, range);
                }
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                if let (Some(bits), Some(r)) = (self.int_bits(ty), first) {
                    let atom = Atom::Cmp {
                        op: *op,
                        bits,
                        lhs: *lhs,
                        rhs: *rhs,
                    };
                    self.conds.insert(
                        r,
                        Cond {
                            atom,
                            negated: false,
                        },
                    );
                }
            }
            Inst::Overflow { op, ty, lhs, rhs } => {
                if let (Some(bits), Some(r)) = (self.int_bits(ty), first) {
                    let (a, b) = (self.cur_or_top(*lhs, bits), self.cur_or_top(*rhs, bits));
                    let wrapping = match op {
                        OverflowOp::AddOverflow => BinOp::Add,
                        OverflowOp::SubOverflow => BinOp::Sub,
                        OverflowOp::MulOverflow => BinOp::Mul,
                    };
                    let signed = ty.is_signed();
                    self.def.insert(r, binop(wrapping, bits, signed, a, b));
                    if let (false, Some(&flag)) = (signed, node.results.get(1)) {
                        let exact = unwrapped(*op, bits, a, b);
                        self.conds.insert(
                            flag,
                            Cond {
                                atom: Atom::Overflowed { result: r, exact },
                                negated: false,
                            },
                        );
                    }
                }
            }
            Inst::Assume { cond } | Inst::Assert { cond, .. } => self.assume(*cond, true),
            Inst::Alloca { ty, count, .. } => self.judge(at, "alloca", ty, *count),
            Inst::HeapAlloc { ty, count, .. } => self.judge(at, "heap_alloc", ty, *count),
            _ => {}
        }
        // Every other integer result is unconstrained.
        if node.results.iter().any(|r| !self.def.contains_key(r)) {
            for (r, ty) in node.results.iter().zip(node.result_tys(self.module)) {
                if !self.def.contains_key(r)
                    && let Some(bits) = self.int_bits(&ty)
                {
                    self.def.insert(*r, Range::top(bits, ty.is_signed()));
                }
            }
        }
    }

    /// Evaluate block `position`'s parameters and instructions; with
    /// `incoming` (a dominator walk), record the ranges its edges pass.
    fn block(&mut self, position: usize, incoming: Option<&[(BlockId, usize)]>) {
        self.census.blocks += 1;
        let func = self.func;
        let block = &func.blocks[position];
        for (k, (v, ty)) in block.params.iter().enumerate() {
            let Some(bits) = self.int_bits(ty) else {
                continue;
            };
            let top = Range::top(bits, ty.is_signed());
            let joined = match incoming {
                Some(edges) if block.id != func.entry && !edges.is_empty() => {
                    edges.iter().try_fold(None::<Range>, |acc, edge| {
                        self.census.arguments_joined += 1;
                        let arg = self
                            .edge_args
                            .get(edge)
                            .and_then(|args| args.get(k).copied().flatten())
                            .filter(|r| r.bits == bits)?;
                        Some(Some(acc.map_or(arg, |acc| acc.join(arg))))
                    })
                }
                _ => None,
            };
            let range = joined.flatten().map_or(top, |r| Range {
                signed: ty.is_signed(),
                ..r
            });
            self.def.insert(*v, range);
        }
        for (index, node) in block.body.iter().enumerate() {
            self.eval((position, index), node);
        }
        if incoming.is_none() {
            return;
        }
        let Some(terminator) = block.body.last() else {
            return;
        };
        for (index, (_, args)) in successors(&terminator.inst).into_iter().enumerate() {
            let facts = self.edge_facts(&terminator.inst, index);
            let ranges = args
                .iter()
                .map(|arg| {
                    facts
                        .iter()
                        .filter(|(subject, _)| subject == arg)
                        .fold(self.cur(*arg), |r, (_, fact)| r.map(|r| r.meet(*fact)))
                })
                .collect();
            self.census.edges_recorded += 1;
            self.edge_args.insert((block.id, index), ranges);
        }
    }

    fn run(&mut self) {
        let dom = DominatorTree::new(self.func);
        if !dom.is_well_formed() {
            // No trustworthy CFG: judge each block alone, with the facts its
            // own `Assume`s / `Assert`s state and nothing from any branch.
            for position in 0..self.func.blocks.len() {
                let mark = self.undo.len();
                self.block(position, None);
                self.undo_to(mark);
            }
            return;
        }
        let func = self.func;
        let positions: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(position, block)| (block.id, position))
            .collect();
        let terminator = |block: BlockId| {
            positions
                .get(&block)
                .and_then(|position| func.blocks[*position].body.last())
        };
        let targets = |block: BlockId| -> Vec<BlockId> {
            terminator(block).map_or_else(Vec::new, |node| {
                successors(&node.inst)
                    .into_iter()
                    .map(|(target, _)| target)
                    .collect()
            })
        };
        // Reverse postorder of the reachable CFG, and each block's incoming
        // edges from reachable blocks (source, successor index).
        let mut rpo_number: HashMap<BlockId, usize> = HashMap::new();
        let mut incoming: HashMap<BlockId, Vec<(BlockId, usize)>> = HashMap::new();
        let mut postorder = Vec::new();
        let mut seen = std::collections::HashSet::from([func.entry]);
        let mut dfs = vec![(func.entry, targets(func.entry), 0usize)];
        while let Some((source, block_targets, next)) = dfs.last_mut() {
            let Some(&target) = block_targets.get(*next) else {
                postorder.push(*source);
                dfs.pop();
                continue;
            };
            incoming.entry(target).or_default().push((*source, *next));
            *next += 1;
            if seen.insert(target) {
                dfs.push((target, targets(target), 0));
            }
        }
        let reachable = postorder.len();
        for (index, block) in postorder.into_iter().enumerate() {
            rpo_number.insert(block, reachable - 1 - index);
        }
        // Dominator-tree children, in reverse postorder: every forward-edge
        // predecessor of a block is then walked before the block.
        let mut children: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
        for block in &func.blocks {
            if let Some(parent) = dom.immediate_dominator(block.id) {
                children.entry(parent).or_default().push(block.id);
            }
        }
        for list in children.values_mut() {
            list.sort_by_key(|block| rpo_number.get(block).copied().unwrap_or(usize::MAX));
        }
        enum Step {
            Enter(BlockId),
            Leave(usize),
        }
        let mut stack = vec![Step::Enter(func.entry)];
        while let Some(step) = stack.pop() {
            let block = match step {
                Step::Leave(mark) => {
                    self.undo_to(mark);
                    continue;
                }
                Step::Enter(block) => block,
            };
            let Some(&position) = positions.get(&block) else {
                continue;
            };
            let mark = self.undo.len();
            let edges = incoming.remove(&block).unwrap_or_default();
            // The edge every path into this block takes holds throughout the
            // region it dominates. Its source is the immediate dominator,
            // whose end state is the state now.
            if let Some(parent) = dom.immediate_dominator(block)
                && let Some(&(_, index)) = edges.iter().find(|(source, index)| {
                    *source == parent && dom.edge_dominates(parent, *index, block)
                })
                && let Some(node) = terminator(parent)
            {
                for (v, fact) in self.edge_facts(&node.inst, index) {
                    self.refine(v, fact);
                }
            }
            self.block(position, Some(&edges));
            stack.push(Step::Leave(mark));
            for child in children.get(&block).into_iter().flatten().rev() {
                stack.push(Step::Enter(*child));
            }
        }
    }
}

#[cfg(test)]
#[path = "alloc_bound_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "alloc_bound_property_tests.rs"]
mod property_tests;

#[cfg(test)]
#[path = "alloc_bound_differential_tests.rs"]
mod differential_tests;

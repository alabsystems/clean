// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! # Fragment-2 — expression DENOTATION `[[.]] : trust-ir fn / kernel Expr -> Nat-mod-2^w Expr`
//!
//! Fragment-1 ([`crate::reflect`]) reflects trust-ir *obligations* (does this
//! instruction panic?). Fragment-2 reflects trust-ir *meaning*: it maps a
//! compiled trust-ir function — and, on the other side, the decl's ORIGINAL
//! kernel definition — into ONE shared arithmetic vocabulary over `Nat`, so
//! that the Clean kernel can DECIDE whether the emitted code denotes the
//! original definition. This is the reflection layer under the backend
//! semantics-preservation (translation-validation) certificate minted by
//! `clean-compiler::emit_trust_ir_tv` and re-checked in-process by
//! `trust_ir_build::validate` (anchor `clean_backend_tv`).
//!
//! ## The fragment (exact, fail-closed outside it)
//!
//! **Emitted side** ([`denote_function`]): a trust-ir function whose signature
//! is `U{8,16,32,64}^n -> U-w` (one uniform width `w`) and whose body is either
//!
//! * **Fragment-2** — a SINGLE block of `Const{U-w, Int k}` (`0 <= k < 2^w`) and
//!   `BinOp{Add|Sub|Mul|And|Or|Xor, U-w}` instructions, nonzero-literal
//!   `URem`, and `Shl|LShr` with a literal or modulo-proved in-range amount,
//!   ending in `Return` of one bound
//!   value; or
//! * **Fragment-3a** — a three-block `CondBr` diamond: an ENTRY block of
//!   Fragment-2 arithmetic plus exactly one `ICmp{Ult|Ule|Ugt|Uge|Eq, U-w}`
//!   feeding a `CondBr` (no branch arguments) into TWO param-free arms, each a
//!   Fragment-2 arithmetic prefix ending in a single-value `Return`.
//!
//! No calls, no memory, no `Switch`/unstructured branches, no casts — anything
//! else is [`ReflectError::Unsupported`] with an auditable label.
//!
//! **Source side** ([`denote_source`]): the decl's kernel definition Expr,
//! `fun (x1 ... xn : UIntW) => body` where `body` is composed of the bound
//! variables, `UIntW.ofNat k` literals (`0 <= k < 2^w`),
//! `UIntW.{add,sub,mul,land,lor,xor,shiftLeft,shiftRight}`, and actual `OfNat`/arithmetic dictionary
//! fields (named dictionaries require the original source environment), and
//! (Fragment-3a) a Bool-comparison conditional — `cond`/`Bool.rec`/`Bool.casesOn`
//! over a `UIntW.{blt,ble,beq}` comparison — and (WS6.6) `let x : UIntW := v; b`,
//! denoted by the kernel's own zeta rule: `[[let x := v; b]] = [[b]][[[v]]/x]`.
//! Ordinary propositional `ite` over an actual UInt LT/LE dictionary field
//! additionally requires a checked equation for the complete original source
//! call; [`denote_source_with_requirements`] reports that obligation to the
//! minter and imported-source validator. XOR and shifts likewise require their
//! complete original-source equation. Shifts reduce the amount modulo the
//! word width before the machine operation; bare unbounded shifts refuse.
//! Their proposed Nat models are not proofs.
//! The comparand therefore stays let-free and inside the vocabulary above, so
//! the pinned trust-ir re-checker (which re-derives only the emitted side and
//! re-runs the kernel on the carried comparand) needs nothing new for it.
//!
//! ## WS6.6: widening is pin-cycle ordered
//!
//! Every EMITTED-side shape added here must first be re-derivable by the
//! trust-ir re-checker this workspace pins (`trust_ir_build`'s
//! `clean_backend_tv` mirror): a certificate for a shape the pinned mirror
//! does not know fails its re-check, and `validate_module_for_codegen` then
//! refuses the whole module, so minting it early would turn a skip into a
//! lost build. The order is (i) clean gains the vocabulary, (ii) trust-ir
//! mirrors it and pins that clean, (iii) clean moves its trust-ir pin and
//! only then mints (trust-ir roadmap WS6.5). A SOURCE-side widening such as
//! `let` is exempt, because the re-checker never re-derives the comparand.
//!
//! The one `Bool` spelling for the widening slices (decision DG-34, shared
//! with the trust-ir mirror): Lean's own `Bool`, exactly what the comparison
//! denotation below already produces. A `Select` denotes `Bool.rec` at the
//! result sort, the Bool connectives are `and`/`or`/`xor`, and `Ne` is the
//! negated `Nat.beq`. Never a `Nat` 0/1 encoding: two spellings would let one
//! side accept an equation the other refuses.
//!
//! ## Control flow — the piecewise vocabulary (Fragment-3a)
//!
//! A two-arm branch on both sides denotes to ONE `Bool.rec` expression:
//!
//! ```text
//! [[if c then t else e]] = Bool.rec.{1} (fun _:Bool => Nat) [[e]] [[t]] [[c]]
//! [[Ult a b]] = Nat.blt [[a]] [[b]]   [[Ule a b]] = Nat.ble [[a]] [[b]]
//! [[Ugt a b]] = Nat.blt [[b]] [[a]]   [[Uge a b]] = Nat.ble [[b]] [[a]]
//! [[Eq  a b]] = Nat.beq [[a]] [[b]]
//! ```
//!
//! The scrutinee `[[c]]` is an OPEN neutral (it mentions the parameters), so the
//! kernel cannot iota-reduce the `Bool.rec`: it decides the equation by matching
//! the two `Bool.rec` applications argument-wise. Swapping the then/else arms, or
//! changing the comparison, therefore yields two genuinely non-def-eq neutrals
//! and the certificate REFUSES (the control-flow miscompile detector).
//!
//! ## Fragment-4 — closed addresses, computing heap
//!
//! Heap reasoning in general needs read-over-write theory (McCarthy
//! select/store). Fragment-4 avoids ALL of it by the Fragment-1 discipline:
//! keep the heap **computable**. Every allocation site in the (straight-line)
//! segment gets a **concrete address** — the reflector numbers `HeapAlloc`s
//! `0, 1, 2, …` and assigns cell base = `alloc_index * BLOCK`, where `BLOCK`
//! is a per-function constant chosen larger than any allocation's size (so
//! distinct allocations never overlap by construction of the *model*, not by
//! an aliasing argument). Every `GEP` has **constant** indices, folded to a
//! closed `Nat` literal offset via the module's `StructDef` layout. Therefore
//! every `Load`/`Store` address is a closed `Nat` literal, and the heap value
//! itself is a closed term over open *stored values*.
//!
//! The vocabulary gains two definitional combinators (no axioms):
//!
//! ```text
//! Heap        := Nat → Nat
//! hempty      := fun _ => 0
//! hwrite h a v := fun a' => Bool.rec (h a') v (Nat.beq a' a)
//! hread h a    := h a
//! ```
//!
//! `hread (hwrite … (hwrite hempty 8 v₁) … 8)` beta/iota-reduces in the
//! kernel: `Nat.beq` on two literals computes, the `Bool.rec` selects, and
//! the read **normalizes to the stored open value expression**. For the whole
//! fragment the heap disappears under reduction — the final equation is
//! between the same `Nat`-mod-`2^w` expressions Fragment-2 already decides.
//! The kernel needs nothing new; `hwrite`/`hread` are *definitions the kernel
//! unfolds* ([`heap_vocab_declarations`]), in the same trust class as
//! `Nat.mod` in the existing vocabulary.
//!
//! ### Emitted-side reflection rules (Fragment-4)
//!
//! Straight-line segment, threading one heap value `H` (initially `hempty`):
//!
//! ```text
//! [[HeapAlloc {origin, size}]]ᵢ  — no term; records base bᵢ = i * BLOCK; result value ↦ literal bᵢ
//! [[GEP p, #k (const path)]]     = literal (addr(p) + offset(path))     (folded; layout from StructDef)
//! [[Store v → a]]                : H ← hwrite H [[a]] [[v]]
//! [[Load a]]                     = hread H [[a]]
//! [[Release a]]                  : structural only — see the honesty notes
//! [[Dealloc a]]                  : REFUSED — a wrong emission (UB on a reference-counted cell)
//! ```
//!
//! A Fragment-4 cell is a reference-counted `CleanHeap` cell, and it is
//! released the one way trust-ir gives meaning to (trust-ir SPEC "A
//! reference-counted cell is released by `Release`, never by `Dealloc`",
//! ratified 2026-09-27): each `HeapAlloc(CleanHeap)` result is released by
//! exactly ONE `Release` of its own result value, in the segment that
//! allocates it. No pointer escapes the fragment and `Retain` / `IsUnique` are
//! outside it, so the count is 1 at that `Release` and it frees the cell. A
//! `Dealloc` of such a cell is undefined behaviour and is refused BY NAME as a
//! [`ReflectError::WrongEmission`] — never an out-of-fragment skip, which is
//! why `Dealloc` stays routed to the heap walker. A `Release` of anything but
//! an allocation's own result value (a GEP alias, a parameter) is out of the
//! fragment.
//!
//! Everything else falls through to the existing Fragment-2/3a/3b rules. Any
//! non-constant GEP index, any pointer arithmetic that does not fold to a
//! literal, any pointer-typed **parameter**, any `Load` whose address is not
//! a recorded live base+offset: **refuse to mint** (fail-closed, the program
//! stays outside the fragment). Heap ops are admitted in the single
//! Fragment-2/3b block and inside Fragment-3a arms where the heap use stays
//! within one arm (each arm threads its own fresh heap; heap ops in the 3a
//! entry prefix fail closed).
//!
//! ### Source-side rules (Fragment-4)
//!
//! The admitted source forms are single-constructor aggregate introduction
//! and field projection (the shapes the ctor lowering compiles to
//! alloc/store/load): a ctor application denotes each field; a projection
//! denotes to the projected field's denotation ([`RecordVocab`]). Pure
//! substitution — the source side never sees the heap. The equation therefore
//! says: *the emitted alloc/store/load choreography computes the same field
//! values the source ctor/projection semantics compute.*
//!
//! ### Why the injections are refused
//!
//! All addresses are literals, so every discrepancy surfaces as a different
//! normal form, and the kernel refuses the equation: a **wrong-offset store**
//! makes the later `hread` reduce past the mis-addressed write to a
//! different field's value (or leaves the loaded cell unwritten — refused by
//! the walker, below); **swapped store order / aliased writes** to the SAME
//! literal address normalize the read to the earlier value; a
//! **load-before-store** (including a **dropped store**) never reaches the
//! kernel at all: the walker REFUSES a `Load` of a never-written cell as a
//! wrong emission, because an uninitialized read is UB in trust-ir's
//! reference semantics and letting it denote to `hempty`'s 0 would wrongly
//! certify a dropped store of literal 0. Writes to distinct addresses
//! commute *after reduction* — which is exactly the semantics, so benign
//! reordering certifies (no false negative).
//!
//! ### Honesty notes (boundary 6 bookkeeping)
//!
//! 1. **The release is invisible to the value equation.** A pure value
//!    denotation cannot observe a cell being freed. Dropped/doubled
//!    `Release`s are refused by a **structural alloc/release balance check in
//!    the minter's emit gate** (`clean-compiler::emit_trust_ir_tv`, mirrored
//!    by trust-ir's `clean_backend_tv` re-checker): exactly one `Release` per
//!    `HeapAlloc` result, no `Dealloc` of an allocation base — NOT by the
//!    kernel equation. The heap fragment's kernel claim is value-correctness;
//!    the release discipline is checked structurally (test evidence, not a
//!    kernel judgment). The walker below contributes the structural liveness
//!    floor: a `Release` must cite its allocation's own result value, a
//!    `Load`/`Store` touching a released cell fails closed, and a `Dealloc`
//!    is refused as a wrong emission.
//!    *Amended 2026-09-28:* until then this note and the walker spelled the
//!    release `Dealloc` and the balance counted `Dealloc`s. trust-ir's SPEC
//!    ruling of 2026-09-27 makes `Dealloc` of a `CleanHeap` cell undefined
//!    behaviour — in trust-ir's reference interpreter for every cell, and in
//!    its Lean model for a scalar cell (Lean's `semDealloc` refuses the
//!    `arcRef` permission a reference-counted origin gets; the aggregate
//!    cells this fragment allocates are `unsupported.layout` in Lean). A
//!    certificate over a `Dealloc`-freed body therefore named a program the
//!    reference interpreter calls UB.
//! 2. **Layout is reflector spec.** The field-index → byte-offset fold reads
//!    `StructDef{offset,size,align}` through trust-ir's own shape queries
//!    (`Module::ty_layout_shape` / `Module::struct_field_offset_bits`) —
//!    shared with, not duplicated from, the reference layout. A wrong fold is
//!    a certificate-soundness bug in these ~50 lines, the same trust class as
//!    the existing maps.
//! 3. **`BLOCK` separation is a model choice, not an aliasing proof.** It
//!    encodes "distinct allocations don't alias" — true of the allocator the
//!    fragment targets (CleanHeap Perceus cells). Pointer identity games
//!    (ptr-to-int, cross-allocation GEP) do not fold to recorded cells and
//!    are refused at mint time.
//!
//! ## Fragment-5 — boxed-`Nat` constants
//!
//! A PARAMETER-FREE `() -> Ptr` body over Clean's boxed-`Nat` runtime rows
//! (`clean_box`, `clean_box_uint32`, `clean_box_uint64`, `clean_nat_of_u64`,
//! `clean_nat_big`, `clean_unbox`, `clean_unbox_uint32`, `clean_unbox_uint64`,
//! `l_Nat_{add,sub,mul,div,mod}`) and closed 0-ary helpers denotes to a
//! closed `Nat` (the Fragment-5 section of the code, `f5_vocab_row`).
//!
//! ### Ownership (Fragment-5)
//!
//! The value denotation cannot see reference counting: `Retain` and `Release`
//! are invisible to it, and so is the runtime consuming a call's arguments.
//! trust-ir's SPEC ("A reference-counted cell is released by `Release`, never
//! by `Dealloc`", clause 4) holds Fragment-5 to Fragment-4's exactly-once
//! discipline, and `f5_ownership_balance` checks it structurally, on every
//! body the walker admits, whether or not the kernel judges its equation:
//!
//! * each `Ptr` call result is an owned reference at count 1, and a `Copy`
//!   names the same reference;
//! * `Retain` adds one; a `Release`, an `l_Nat_*` argument and the `Return`
//!   each give one up; a `clean_unbox*` argument only reads the reference;
//! * every operation needs a live reference, and the body ends holding none;
//!   each inlined helper is held to this on its own body.
//!
//! A violation (use after free, count underflow, a leak) is a
//! [`ReflectError::WrongEmission`], which the minter refuses as a detected
//! miscompile. Evidence class: TEST — the balance tests in `denote_tests.rs`
//! and the minter's Fragment-5 tests — never a kernel judgment. The
//! consume/borrow table (`f5_consumes_ptr_args`, `f5_borrows_ptr_arg`) is
//! checker spec transcribed from `clean-cli`'s `native_build.rs` shims and
//! `clean-runtime`'s `clean_runtime.c` / `clean_runtime.h`; nothing checks the
//! runtime against it. The balance treats a tagged immediate like a heap cell,
//! which is stricter than the runtime needs.
//!
//! trust-ir's `clean_backend_tv` has no Fragment-5 (it refuses a `Ptr`
//! return), so Clean's minter decides a Fragment-5 equation in the kernel and
//! applies this balance, but mints no certificate for it
//! (`emit_trust_ir_tv::FRAGMENT5_NOT_MINTED` in `clean-compiler`).
//!
//! ## The shared vocabulary (the checker's spec)
//!
//! With `M = 2^w`:
//!
//! ```text
//! [[x_i]]        = bvar                        (the i-th Nat binder)
//! [[k]]          = Nat literal k               (requires k < M)
//! [[add a b]]    = Nat.mod (Nat.add [[a]] [[b]]) M
//! [[mul a b]]    = Nat.mod (Nat.mul [[a]] [[b]]) M
//! [[sub a b]]    = Nat.mod (Nat.sub (Nat.add [[a]] M) [[b]]) M
//! ```
//!
//! This is exactly trust-ir's RATIFIED integer semantics (Add/Sub/Mul wrap
//! two's-complement at the operand width — trust-ir `docs/ub-numerics-policy.md`)
//! expressed over `Nat`, and it is simultaneously the standard `toNat`
//! denotation of the kernel's fixed-width `UIntW` operations (`UIntW` is
//! `Fin (2^w)`-based: `add`/`mul` are mod-`2^w`, `sub` is `(a + 2^w - b) mod
//! 2^w`). The `Nat.sub` in the sub-arm never truncates on the denoted domain:
//! `[[a]] + M >= M > [[b]]` whenever `[[b]] < M`, which holds for every
//! denotation the fragment can produce over arguments `< M`.
//!
//! ## Trust status — stated honestly
//!
//! The two denotation maps are PART OF THE CHECKER'S SPEC, exactly like
//! Fragment-1's overflow vocabulary: the kernel decides the *equation between
//! the two denotations*; it does not (today) decide that either map is
//! faithful to its side. What backs each map:
//!
//! * emitted side — trust-ir's ratified numerics policy (the wrapping table in
//!   `docs/ub-numerics-policy.md`) and its Lean/`interpret` semantics, which
//!   this vocabulary transcribes 1:1;
//! * source side — the kernel's `UIntW = Fin (2^w)` definitions, which this
//!   vocabulary transcribes 1:1 under `toNat`.
//!
//! DEFERRED (not claimed): a mechanized proof, inside clean-kernel, that
//! `[[e]] = (eval e).toNat` for the source map and a Lean-level bisimulation
//! for the emitted map. Until then a bug in the ~200 lines below is a
//! soundness bug of the CERTIFICATE (not of the kernel), the same trust class
//! as Fragment-1's `ayAddOverflows` boundary — small, named, auditable.
//!
//! The denotation quantifies over ALL of `Nat`; its faithfulness to a machine
//! execution is on the U-w domain (arguments `< 2^w`), which is what the U-w
//! parameter types enforce at every call boundary.

use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Literal, Name};
use trust_ir::constant::Constant;
use trust_ir::inst::{AllocOrigin, BinOp, ICmpOp, Inst};
use trust_ir::ty::Ty;
use trust_ir::{BlockId, Function, Module, ValueId};

use crate::error::ReflectError;

/// `Inst::A { .. } | Inst::B { .. } | …` over NAMED [`Inst`] variants
/// (`{ .. }` matches unit and tuple variants as well).
///
/// Every `Inst` dispatch in this file ends in a refusal arm spelled through
/// this instead of an `other =>` catch-all, so a variant trust-ir adds fails
/// to compile AT EACH DISPATCH until someone decides whether that dispatch
/// denotes it — rather than joining its refusal unseen.
macro_rules! insts {
    ($($variant:ident),+ $(,)?) => { $(Inst::$variant { .. })|+ };
}

#[path = "scalar_denote.rs"]
mod scalar;
pub use scalar::{denote_scalar_function, ScalarDenotation, ScalarSort};

/// The in-process kernel anchor identifier for the backend
/// translation-validation certificate. MUST stay byte-identical to trust-ir's
/// `trust_ir::proof::KERNEL_ANCHOR_CLEAN_BACKEND_TV` — the re-checker rejects
/// every other anchor string fail-closed.
pub const CLEAN_BACKEND_TV_ANCHOR: &str = "clean_backend_tv";

/// A Fragment denotation: `arity` `Nat`-param binders over `body` at width
/// `width`, plus (Fragment-3b) `callees` — the pinned callee symbols the body
/// references.
///
/// `body` is a kernel `Expr` over de Bruijn `bvar`s. The full binder telescope
/// is `G_0 … G_{m-1} x_0 … x_{n-1}` (callee symbols OUTERMOST, then params):
/// parameter `i` (0-based) appears as `bvar(arity - 1 - i)` — unchanged from
/// Fragment-2, since the callee binders sit ABOVE the params — and the `j`-th
/// callee symbol appears as `bvar(arity + (callees.len() - 1 - j))`, applied to
/// its argument denotations. `callees[j] = (name, callee_arity)` for a callee
/// symbol `G_j : Nat^callee_arity → Nat`. Fragment-2/3a leave `callees` empty.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct TvDenotation {
    /// Number of parameters (the innermost `arity` binders of the telescope).
    pub arity: usize,
    /// The uniform unsigned bit-width `w` of the fragment (8, 16, 32, or 64).
    pub width: u32,
    /// The denotation body over the binder telescope.
    pub body: Expr,
    /// The pinned callee symbols `(name, callee_arity)`, in a canonical order
    /// (sorted by name), each bound as an OUTER `Nat^callee_arity → Nat` symbol.
    /// Empty for the call-free fragments.
    pub callees: Vec<(String, usize)>,
}

/// `2^w` as a kernel `Nat` literal (the fragment modulus).
pub fn modulus(width: u32) -> Expr {
    match width {
        w @ (8 | 16 | 32) => Expr::nat_lit(1u64 << w),
        64 => Expr::nat_lit_u128(1u128 << 64),
        w => unreachable!("fragment widths are 8/16/32/64, got {w}"),
    }
}

/// The fragment width of an unsigned trust-ir scalar type, if any.
fn width_of_ty(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::Ext(e) => e.unreachable(),
        Ty::U8 => Some(8),
        Ty::U16 => Some(16),
        Ty::U32 => Some(32),
        Ty::U64 => Some(64),
        // Every other type NAMED: a scalar trust-ir adds must be classified
        // here before it can reach -- or be kept out of -- the fragment.
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U128
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Vector(..)
        | Ty::Tensor(..)
        | Ty::Ptr
        | Ty::FatPtr(_)
        | Ty::Unit
        | Ty::Never
        | Ty::Struct(_)
        | Ty::Array(..)
        | Ty::Tuple(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::FnItem(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(..)
        | Ty::Dialect(_)
        | Ty::Storage(_)
        | Ty::Handle(_) => None,
    }
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn nat_app2(f: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str(f), [a, b])
}

/// `Nat.mod e M` — the wrap-to-width step of the shared vocabulary.
fn wrap(e: Expr, m: &Expr) -> Expr {
    nat_app2("Nat.mod", e, m.clone())
}

/// The shared vocabulary's binary-op denotation (see module docs).
#[path = "denote_source_instances.rs"]
mod source_instances;
use source_instances::SourceInstances;

fn denote_binop(op: BinOp, a: Expr, b: Expr, m: &Expr) -> Result<Expr, ReflectError> {
    // These are syntactic facts about the actual denotation, not annotations
    // supplied by the emitter. The independent IR reader separately derives
    // its own nonzero/range facts from instruction dataflow.
    let literal = |e: &Expr| match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        // Every rejected expression is named so a new kernel variant must
        // be reviewed before it can contribute a literal range fact.
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(..)
        | ExprKind::App(..)
        | ExprKind::Lam(..)
        | ExprKind::Pi(..)
        | ExprKind::Let(..)
        | ExprKind::Lit(Literal::String(_))
        | ExprKind::Proj(..)
        | ExprKind::MData(..)
        | ExprKind::SProp
        | ExprKind::Squash(_)
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::CubicalPath { .. }
        | ExprKind::CubicalPathLam { .. }
        | ExprKind::CubicalPathApp { .. }
        | ExprKind::CubicalHComp { .. }
        | ExprKind::CubicalTransp { .. }
        | ExprKind::CubicalCoe { .. }
        | ExprKind::ZFCSet(_)
        | ExprKind::ZFCMem { .. }
        | ExprKind::ZFCComprehension { .. } => None,
    };
    let width = [8u32, 16, 32, 64].into_iter().find(|w| modulus(*w) == *m);
    let shift_in_range = || {
        let Some(width) = width else {
            return false;
        };
        if let Some(k) = literal(&b) {
            return k < u64::from(width);
        }
        let args = b.get_app_args();
        is_const_named(b.get_app_fn(), "Nat.mod")
            && args.len() == 2
            && literal(args[1]).is_some_and(|n| n > 0 && n <= u64::from(width))
    };
    Ok(match op {
        BinOp::Add => wrap(nat_app2("Nat.add", a, b), m),
        BinOp::Mul => wrap(nat_app2("Nat.mul", a, b), m),
        BinOp::And => nat_app2("Nat.land", a, b),
        BinOp::Or => nat_app2("Nat.lor", a, b),
        BinOp::Xor => nat_app2("Nat.xor", a, b),
        BinOp::URem if literal(&b).is_some_and(|n| n > 0) => nat_app2("Nat.mod", a, b),
        BinOp::Shl if shift_in_range() => wrap(
            nat_app2("Nat.mul", a, nat_app2("Nat.pow", Expr::nat_lit(2), b)),
            m,
        ),
        BinOp::LShr if shift_in_range() => {
            nat_app2("Nat.div", a, nat_app2("Nat.pow", Expr::nat_lit(2), b))
        }
        // Wrapping sub over Nat: (a + M - b) mod M. `Nat.sub` is monus, but
        // `a + M >= M > b` on the denoted domain, so it never truncates here.
        BinOp::Sub => wrap(nat_app2("Nat.sub", nat_app2("Nat.add", a, m.clone()), b), m),
        // Every other BinOp is outside Fragment-2 and refuses. Listed rather
        // than wildcarded so a BinOp trust-ir adds later fails to compile here
        // instead of joining the refusal unexamined — the WS3.20 rotates and
        // copySign (trust-ir 4f09dab8) are the latest to be named.
        BinOp::UDiv
        | BinOp::SDiv
        | BinOp::URem
        | BinOp::SRem
        | BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax
        | BinOp::Shl
        | BinOp::LShr
        | BinOp::AShr
        | BinOp::BAnd
        | BinOp::BOr
        | BinOp::BXor
        | BinOp::RotL
        | BinOp::RotR
        | BinOp::FCopySign => {
            return Err(ReflectError::unsupported(format!(
                "BinOp {op:?} is outside Fragment-2 or lacks a literal nonzero divisor / proved shift bound (fail-closed)"
            )));
        }
    })
}

// --- Fragment-3a: control flow (one CondBr, two return paths) ----------------
//
// The emitted 3-block CFG `entry -> {then, else}` and the source `if cmp then a
// else b` both denote into ONE piecewise expression over the shared vocabulary:
//
// ```text
// [[if c then t else e]] = Bool.rec.{1} (fun _ : Bool => Nat) [[e]] [[t]] [[c]]
// ```
//
// i.e. `false -> [[e]]`, `true -> [[t]]` — the standard `toNat`/`Bool.rec`
// semantics of a two-arm branch (false minor first, then true minor, then the
// scrutinee, exactly as `clean_kernel`'s `Bool.rec` is applied). The condition
// `[[c]]` is a Bool-valued Nat comparison (`Nat.blt`/`Nat.ble`/`Nat.beq`),
// itself the transcription of trust-ir's unsigned `ICmp` on the U-w domain (a
// U-w value's `toNat` is `< 2^w`, so the Nat comparison agrees with the machine
// comparison). The two arms are Fragment-2 arithmetic denotations. Because the
// `Bool.rec` scrutinee is an OPEN neutral (it mentions the parameters), the
// kernel cannot iota-reduce it: it decides the equation by comparing the two
// `Bool.rec` applications argument-wise — so swapping the then/else arms, or
// changing the comparison, yields two genuinely non-def-eq neutrals and the
// certificate REFUSES (verified by test).

/// `Bool` as a kernel constant.
fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}

/// The shared if-denotation `Bool.rec.{1} (fun _:Bool => Nat) else_e then_e cond`.
fn ite_nat(cond: Expr, then_e: Expr, else_e: Expr) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, bool_ty(), nat());
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [motive, else_e, then_e, cond],
    )
}

/// The shared vocabulary's UNSIGNED integer-comparison denotation. Signed
/// comparisons and `Ne` are outside Fragment-3a (fail-closed).
fn denote_icmp(op: ICmpOp, a: Expr, b: Expr) -> Result<Expr, ReflectError> {
    Ok(match op {
        ICmpOp::Ult => nat_app2("Nat.blt", a, b),
        ICmpOp::Ule => nat_app2("Nat.ble", a, b),
        ICmpOp::Ugt => nat_app2("Nat.blt", b, a),
        ICmpOp::Uge => nat_app2("Nat.ble", b, a),
        ICmpOp::Eq => nat_app2("Nat.beq", a, b),
        other @ (ICmpOp::Ne | ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge) => {
            return Err(ReflectError::unsupported(format!(
                "ICmp {other:?} (Fragment-3a covers unsigned Ult/Ule/Ugt/Uge/Eq only, \
                 fail-closed)"
            )));
        }
    })
}

// --- Fragment-3b: calls (compositional translation validation) ---------------
//
// A `Call g(a…)` in the emitted body — and the matching `g a…` application in
// the source — both denote to ONE PINNED SYMBOL `G_g` applied to the argument
// denotations. `G_g` is an OUTER `∀`-bound variable `Nat^arity → Nat` standing
// for g's own certified denotation ("uninterpreted but pinned"): the caller
// equation `∀ G_g … x, ⟦caller emit⟧ = ⟦caller src⟧` is decided by the kernel
// FOR ALL interpretations of `G_g`, so it holds in particular at g's true
// meaning — which g's OWN translation-validation certificate establishes,
// composed via `ProofEvidence::InheritedFromCallee`. Miscompiling the caller's
// composition (wrong constant, wrong callee, wrong argument) makes the two
// denotations differ and the kernel REFUSES.

use std::collections::{BTreeMap, BTreeSet};

/// The de Bruijn index of the `j`-th callee symbol `G_j` in a telescope with
/// `param_arity` params (innermost) and `callee_count` callee symbols
/// (outermost).
fn callee_symbol_bvar(param_arity: usize, callee_count: usize, j: usize) -> u32 {
    #[allow(clippy::cast_possible_truncation)]
    {
        (param_arity + (callee_count - 1 - j)) as u32
    }
}

/// `Nat^ca → Nat` — the kernel type of a pinned callee symbol of arity `ca`.
fn callee_fn_ty(ca: usize) -> Expr {
    (0..ca).fold(nat(), |acc, _| Expr::arrow(nat(), acc))
}

/// Scan a single-block function's `Call` sites, returning the canonical
/// callee list (sorted by name, deduplicated) and a `name -> symbol bvar`
/// map, for a telescope with `param_arity` params. Fail-closed on a dangling
/// callee `FuncId` or a name whose call sites disagree on arity.
fn scan_callees(
    module: &Module,
    block: &trust_ir::Block,
    param_arity: usize,
) -> Result<(Vec<(String, usize)>, BTreeMap<String, u32>), ReflectError> {
    let mut arity_of: BTreeMap<String, usize> = BTreeMap::new();
    for node in &block.body {
        if let Inst::Call { callee, args } = &node.inst {
            let f = module
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .ok_or_else(|| {
                    ReflectError::Malformed(format!("Call targets missing function {callee:?}"))
                })?;
            match arity_of.get(&f.name) {
                Some(a) if *a != args.len() => {
                    return Err(ReflectError::unsupported(format!(
                        "callee `{}` is called with inconsistent arities ({a} vs {}) — \
                         fail-closed",
                        f.name,
                        args.len()
                    )));
                }
                _ => {
                    arity_of.insert(f.name.clone(), args.len());
                }
            }
        }
    }
    // BTreeMap iterates sorted by name — the canonical order both sides use.
    let callees: Vec<(String, usize)> = arity_of.into_iter().collect();
    let mut symbol_of = BTreeMap::new();
    for (j, (name, _)) in callees.iter().enumerate() {
        symbol_of.insert(
            name.clone(),
            Expr::bvar(callee_symbol_bvar(param_arity, callees.len(), j)),
        );
    }
    // Return symbol bvars keyed by name; store the raw index in a parallel map.
    let mut idx_of = BTreeMap::new();
    for (name, e) in &symbol_of {
        if let ExprKind::BVar(i) = e.kind() {
            idx_of.insert(name.clone(), *i);
        }
    }
    Ok((callees, idx_of))
}

// --- Fragment-4: closed-address computing heap --------------------------------
//
// See the module docs for the model. The walker below is the emitted-side
// implementation: an alloc table with concrete bases (`i * BLOCK`), GEPs
// folded to closed `Nat` literals via trust-ir's own layout queries, and ONE
// heap term threaded through the straight-line segment. Anything that does
// not fold is `ReflectError::Unsupported` (fail-closed — the program stays
// outside the fragment).

/// Kernel constant name of the empty heap `fun _ => 0` (Fragment-4).
pub const HEAP_HEMPTY: &str = "CleanTV.hempty";
/// Kernel constant name of the heap write combinator (Fragment-4).
pub const HEAP_HWRITE: &str = "CleanTV.hwrite";
/// Kernel constant name of the heap read combinator (Fragment-4).
pub const HEAP_HREAD: &str = "CleanTV.hread";

/// `Nat → Nat` — the kernel type of a Fragment-4 heap value.
fn heap_fn_ty() -> Expr {
    Expr::arrow(nat(), nat())
}

/// The empty-heap term `CleanTV.hempty`.
pub fn hempty() -> Expr {
    Expr::const_str(HEAP_HEMPTY)
}

/// `CleanTV.hwrite h a v` — the heap with `v` stored at address `a`.
pub fn hwrite(h: Expr, addr: Expr, v: Expr) -> Expr {
    Expr::apps(Expr::const_str(HEAP_HWRITE), [h, addr, v])
}

/// `CleanTV.hread h a` — the value stored at address `a`.
pub fn hread(h: Expr, addr: Expr) -> Expr {
    Expr::apps(Expr::const_str(HEAP_HREAD), [h, addr])
}

/// The three DEFINITIONAL heap combinators (no axioms — the kernel unfolds
/// them), exactly the module-doc vocabulary:
///
/// ```text
/// hempty      := fun _ => 0
/// hwrite h a v := fun a' => Bool.rec (h a') v (Nat.beq a' a)
/// hread h a    := h a
/// ```
///
/// Install these into the prelude environment before adding a Fragment-4 TV
/// theorem. The trust-ir re-checker is INTENDED to install the identical
/// declarations on its side (duplicated there BY DESIGN, like the walker),
/// but that vocabulary has NOT landed in trust-ir yet: until it does, an
/// independent recheck of a heap-fragment certificate REJECTS on the unknown
/// `CleanTV.h*` constants (fail-closed — never wrongly accepts).
#[must_use]
pub fn heap_vocab_declarations() -> Vec<Declaration> {
    // hwrite body over binders h a v a' (a' innermost = bvar 0):
    // Bool.rec (motive := fun _ => Nat) (h a') v (Nat.beq a' a)
    let beq = nat_app2("Nat.beq", Expr::bvar(0), Expr::bvar(2));
    let h_at = Expr::app(Expr::bvar(3), Expr::bvar(0));
    let hwrite_body = ite_nat(beq, Expr::bvar(1), h_at);
    let hwrite_value = Expr::lam(
        BinderInfo::Default,
        heap_fn_ty(),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, nat(), hwrite_body),
            ),
        ),
    );
    vec![
        Declaration::Definition {
            name: Name::from_string(HEAP_HEMPTY),
            level_params: vec![],
            type_: heap_fn_ty(),
            value: Expr::lam(BinderInfo::Default, nat(), Expr::nat_lit(0)),
            is_reducible: true,
        },
        Declaration::Definition {
            name: Name::from_string(HEAP_HWRITE),
            level_params: vec![],
            type_: Expr::arrow(
                heap_fn_ty(),
                Expr::arrow(nat(), Expr::arrow(nat(), heap_fn_ty())),
            ),
            value: hwrite_value,
            is_reducible: true,
        },
        Declaration::Definition {
            name: Name::from_string(HEAP_HREAD),
            level_params: vec![],
            type_: Expr::arrow(heap_fn_ty(), Expr::arrow(nat(), nat())),
            value: Expr::lam(
                BinderInfo::Default,
                heap_fn_ty(),
                Expr::lam(
                    BinderInfo::Default,
                    nat(),
                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
            is_reducible: true,
        },
    ]
}

/// One allocation-site entry in the walker's alloc table.
struct AllocEntry {
    /// Concrete model base address: `alloc_index * BLOCK`.
    // Recorded at HeapAlloc for the audit shape of the alloc table; the walker
    // currently reaches every base through `HeapWalk::addr` instead, so no
    // reader exists yet. Kept — the Fragment-4 release/aliasing checks named in
    // the module header are the pending readers — 2026-07-31.
    #[allow(dead_code)]
    base: u64,
    /// The recorded cell addresses (base + word-sized field offsets).
    cells: Vec<u64>,
    /// Structurally live: `false` once a `Release` of the allocation's own
    /// result value is seen (the fragment's count is 1 there, so that
    /// `Release` frees the cell). The walker tolerates repeated `Release`s of
    /// the same base — dropped and doubled `Release`s are the emit gate's
    /// balance check to REFUSE (honesty note 1), not the walker's to hide by
    /// skipping. A `Dealloc` never reaches this flag: the walker refuses it
    /// as a wrong emission.
    live: bool,
}

/// Fragment-4 walker state for ONE straight-line segment (the single
/// Fragment-2/3b block, or one Fragment-3a arm): the alloc table, folded
/// pointer addresses, closed GEP-index constants, and the threaded heap term.
struct HeapWalk<'a> {
    module: &'a Module,
    /// The per-function `BLOCK` constant (see [`heap_block_constant`]).
    block: u64,
    /// Allocation sites numbered `0, 1, 2, …` in segment order.
    next_alloc: u64,
    /// Alloc result value -> allocation entry.
    allocs: BTreeMap<u32, AllocEntry>,
    /// Folded pointer value -> (owning alloc's result value, closed address).
    /// Tracking the owner is what refuses cross-allocation GEP games: a
    /// folded address is only dereferenceable at its OWN allocation's cells.
    addr: BTreeMap<u32, (u32, u64)>,
    /// Closed unsigned-integer constants usable as GEP indices.
    concrete: BTreeMap<u32, u64>,
    /// Cells a `Store` has written. A `Load` of an address NOT in this set is
    /// an uninitialized read — UB in trust-ir's reference semantics — and is
    /// a [`ReflectError::WrongEmission`], never a denotation: letting it
    /// denote to `hempty`'s 0 would wrongly certify a lowering that dropped a
    /// store of literal 0. (Addresses never recur across allocations: bases
    /// are `next_alloc * BLOCK` and strictly increase.)
    written: BTreeSet<u64>,
    /// The threaded heap term (initially [`hempty`]).
    heap: Expr,
}

impl<'a> HeapWalk<'a> {
    fn new(module: &'a Module, block: u64) -> Self {
        HeapWalk {
            module,
            block,
            next_alloc: 0,
            allocs: BTreeMap::new(),
            addr: BTreeMap::new(),
            concrete: BTreeMap::new(),
            written: BTreeSet::new(),
            heap: hempty(),
        }
    }

    /// Resolve `ptr` to a closed address that is a RECORDED LIVE CELL of its
    /// own allocation — the dereference gate for `Load`/`Store`.
    fn resolve_cell(&self, ptr: ValueId, op: &str) -> Result<u64, ReflectError> {
        let (owner, a) = self.addr.get(&ptr.index()).copied().ok_or_else(|| {
            ReflectError::unsupported(format!(
                "{op} address does not fold to a closed allocation address (fail-closed)"
            ))
        })?;
        let entry = self.allocs.get(&owner).ok_or_else(|| {
            ReflectError::Malformed(format!("{op} address owner is not in the alloc table"))
        })?;
        if !entry.live {
            return Err(ReflectError::unsupported(format!(
                "{op} touches a released allocation (fail-closed)"
            )));
        }
        if !entry.cells.contains(&a) {
            return Err(ReflectError::unsupported(format!(
                "{op} address {a} is not a recorded live cell of its allocation (fail-closed)"
            )));
        }
        Ok(a)
    }
}

/// Per-function `BLOCK` constant: the smallest multiple of 8 STRICTLY larger
/// than the largest `HeapAlloc` size in the function (bytes), so distinct
/// allocations never overlap by construction of the model. Deterministic —
/// the trust-ir re-checker derives the identical constant.
fn heap_block_constant(module: &Module, func: &Function) -> Result<u64, ReflectError> {
    let mut max_size: u64 = 0;
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::HeapAlloc { ty, .. } = &node.inst {
                max_size = max_size.max(ty_size_bytes(module, ty)?);
            }
        }
    }
    Ok((max_size / 8 + 1) * 8)
}

/// Byte size of a type via trust-ir's OWN layout query (honesty note 2: the
/// fold is shared with, not duplicated from, `trust_ir::shape`).
fn ty_size_bytes(module: &Module, ty: &Ty) -> Result<u64, ReflectError> {
    let shape = module.ty_layout_shape(ty).map_err(|e| {
        // A contradictory recorded layout is a wrong emission, not an
        // unsupported fragment. Newer IR queries detect it before alloc_cells
        // reaches its offset checks; preserve the mint gate's refusal class.
        let message = format!("type {ty} has no computable layout ({e}) — fail-closed");
        match e {
            trust_ir::LayoutError::StructLayoutIncoherent(_) => {
                ReflectError::WrongEmission(message)
            }
            trust_ir::LayoutError::MissingType(_)
            | trust_ir::LayoutError::MissingStruct(_)
            | trust_ir::LayoutError::MissingStructSize(_)
            | trust_ir::LayoutError::MissingStructAlign(_)
            | trust_ir::LayoutError::TupleLayoutIncoherent(_)
            | trust_ir::LayoutError::TupleLayoutTargetMissing
            | trust_ir::LayoutError::ClosureLayoutIncoherent(_)
            | trust_ir::LayoutError::ClosureLayoutTargetMissing
            | trust_ir::LayoutError::ClosureCast { .. }
            | trust_ir::LayoutError::TargetScalarLayoutUnavailable { .. }
            | trust_ir::LayoutError::MissingFieldOffset { .. }
            | trust_ir::LayoutError::EnumLayoutUnavailable(_)
            | trust_ir::LayoutError::TyLayoutCycle(_)
            | trust_ir::LayoutError::UnsupportedTyShape(_)
            | trust_ir::LayoutError::SizeOverflow
            | trust_ir::LayoutError::NotPointer(_)
            | trust_ir::LayoutError::OpaqueHandleCast { .. }
            | trust_ir::LayoutError::BoolLaneReinterpret { .. }
            | trust_ir::LayoutError::PointerLaneMismatch { .. }
            | trust_ir::LayoutError::PointerMetadataMismatch { .. }
            | trust_ir::LayoutError::NotFunctionPointerSource(_)
            | trust_ir::LayoutError::CastSizeMismatch { .. } => ReflectError::unsupported(message),
        }
    })?;
    Ok(shape.size_bits.div_ceil(8))
}

/// Cap on recorded cells per allocation — keeps the walker's footprint (and
/// the certificate's tower depth) within the note's ≤10-field budget class.
const MAX_ALLOC_CELLS: usize = 64;

/// The recorded cell addresses of an allocation of `ty` at `base`: word-sized
/// (width-`w`) fields only. Struct field offsets come from the module's
/// `StructDef` layout ([`Module::struct_field_offset_bits`]); arrays scale by
/// the element width; a bare `U-w` scalar is one cell. Fail-closed otherwise.
fn alloc_cells(module: &Module, ty: &Ty, width: u32, base: u64) -> Result<Vec<u64>, ReflectError> {
    let word = u64::from(width / 8);
    let cell = |off: u64| -> Result<u64, ReflectError> {
        base.checked_add(off).ok_or_else(|| {
            ReflectError::unsupported("allocation cell address overflows (fail-closed)".to_string())
        })
    };
    // A bare U-`width` scalar is one cell. Decided BEFORE the dispatch, not
    // as a guarded binding inside it: a guarded binding is a catch-all to
    // clippy's wildcard lint, and it is not one to the reader either.
    if width_of_ty(ty) == Some(width) {
        return Ok(vec![base]);
    }
    match ty {
        Ty::Ext(e) => e.unreachable(),
        Ty::Struct(sid) => {
            let sd = module
                .structs
                .iter()
                .find(|sd| sd.id == *sid)
                .ok_or_else(|| {
                    ReflectError::Malformed(format!("HeapAlloc of missing struct {sid:?}"))
                })?;
            if sd.fields.len() > MAX_ALLOC_CELLS {
                return Err(ReflectError::unsupported(format!(
                    "struct `{}` has {} fields (> {MAX_ALLOC_CELLS}, fail-closed)",
                    sd.name,
                    sd.fields.len()
                )));
            }
            let mut offs = Vec::with_capacity(sd.fields.len());
            for (j, field) in sd.fields.iter().enumerate() {
                if width_of_ty(&field.ty) != Some(width) {
                    return Err(ReflectError::unsupported(format!(
                        "struct `{}` field `{}` has type {} (Fragment-4 cells are \
                         width-U{width} words only, fail-closed)",
                        sd.name, field.name, field.ty
                    )));
                }
                #[allow(clippy::cast_possible_truncation)]
                let off_bits = module
                    .struct_field_offset_bits(*sid, j as u32)
                    .map_err(|e| {
                        ReflectError::unsupported(format!(
                            "struct `{}` field `{}` has no recorded offset ({e}) — fail-closed",
                            sd.name, field.name
                        ))
                    })?;
                offs.push(off_bits / 8);
            }
            // Layout self-consistency (certificate-soundness-critical): the
            // model maps each recorded offset to an independent Nat cell, so
            // a layout table whose fields overlap or fall outside the
            // recorded size would alias machine bytes the model treats as
            // disjoint (or place a cell inside ANOTHER allocation's BLOCK).
            // A correct lowering never records such a table — wrong emission.
            let size = ty_size_bytes(module, ty)?;
            let mut sorted = offs.clone();
            sorted.sort_unstable();
            for pair in sorted.windows(2) {
                if pair[1] - pair[0] < word {
                    return Err(ReflectError::WrongEmission(format!(
                        "struct `{}` records overlapping U{width} fields at byte offsets \
                         {} and {}",
                        sd.name, pair[0], pair[1]
                    )));
                }
            }
            if let Some(&last) = sorted.last() {
                if last.checked_add(word).is_none_or(|end| end > size) {
                    return Err(ReflectError::WrongEmission(format!(
                        "struct `{}` records a field at byte offset {last} outside its \
                         recorded size {size}",
                        sd.name
                    )));
                }
            }
            offs.into_iter().map(cell).collect()
        }
        Ty::Array(elem_id, n) => {
            let elem = module.types.get(elem_id.as_usize()).ok_or_else(|| {
                ReflectError::Malformed(format!("HeapAlloc of array with dangling {elem_id:?}"))
            })?;
            if width_of_ty(elem) != Some(width) {
                return Err(ReflectError::unsupported(format!(
                    "array element type {elem} (Fragment-4 cells are width-U{width} words \
                     only, fail-closed)"
                )));
            }
            if *n as usize > MAX_ALLOC_CELLS {
                return Err(ReflectError::unsupported(format!(
                    "array of {n} elements (> {MAX_ALLOC_CELLS}, fail-closed)"
                )));
            }
            (0..*n).map(|i| cell(i * word)).collect()
        }
        // Every other type NAMED (the scalars included: one whose width is not
        // `width` lands here past the test above).
        other @ (Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Vector(..)
        | Ty::Tensor(..)
        | Ty::Ptr
        | Ty::FatPtr(_)
        | Ty::Unit
        | Ty::Never
        | Ty::Tuple(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::FnItem(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(..)
        | Ty::Dialect(_)
        | Ty::Storage(_)
        | Ty::Handle(_)) => Err(ReflectError::unsupported(format!(
            "HeapAlloc of type {other} (Fragment-4 allocates U{width} words, U{width}-field \
             structs, and U{width} arrays only, fail-closed)"
        ))),
    }
}

/// Fold ONE heap instruction into the walker state (the Fragment-4
/// emitted-side reflection rules — see the module docs table).
fn eval_heap_node(
    node: &trust_ir::InstrNode,
    width: u32,
    den: &mut BTreeMap<u32, Expr>,
    hw: &mut HeapWalk<'_>,
) -> Result<(), ReflectError> {
    match &node.inst {
        Inst::HeapAlloc {
            ty,
            count,
            align: _,
            origin,
        } => {
            if *origin != AllocOrigin::CleanHeap {
                return Err(ReflectError::unsupported(format!(
                    "HeapAlloc origin {origin:?} (Fragment-4 is CleanHeap only, fail-closed)"
                )));
            }
            if count.is_some() {
                return Err(ReflectError::unsupported(
                    "HeapAlloc with a runtime count (fail-closed)".to_string(),
                ));
            }
            let [r] = node.results.as_slice() else {
                return Err(ReflectError::Malformed(
                    "HeapAlloc without exactly one result".to_string(),
                ));
            };
            let base = hw.next_alloc.checked_mul(hw.block).ok_or_else(|| {
                ReflectError::unsupported("allocation base overflows (fail-closed)".to_string())
            })?;
            let cells = alloc_cells(hw.module, ty, width, base)?;
            hw.next_alloc += 1;
            hw.allocs.insert(
                r.index(),
                AllocEntry {
                    base,
                    cells,
                    live: true,
                },
            );
            hw.addr.insert(r.index(), (r.index(), base));
            Ok(())
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds: _,
        } => {
            let (owner, base_addr) = hw.addr.get(&base.index()).copied().ok_or_else(|| {
                ReflectError::unsupported(
                    "GEP base does not fold to a closed allocation address (fail-closed)"
                        .to_string(),
                )
            })?;
            let mut sum: u64 = 0;
            for ix in indices {
                let k = hw.concrete.get(&ix.index()).copied().ok_or_else(|| {
                    ReflectError::unsupported("non-constant GEP index (fail-closed)".to_string())
                })?;
                sum = sum.checked_add(k).ok_or_else(|| {
                    ReflectError::unsupported("GEP index sum overflows (fail-closed)".to_string())
                })?;
            }
            // trust-ir GEP semantics: base + (Σ indices) * size_of(pointee).
            let addr = sum
                .checked_mul(ty_size_bytes(hw.module, pointee_ty)?)
                .and_then(|off| base_addr.checked_add(off))
                .ok_or_else(|| {
                    ReflectError::unsupported("GEP address overflows (fail-closed)".to_string())
                })?;
            let [r] = node.results.as_slice() else {
                return Err(ReflectError::Malformed(
                    "GEP without exactly one result".to_string(),
                ));
            };
            hw.addr.insert(r.index(), (owner, addr));
            Ok(())
        }
        Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align: _,
        } => {
            if *volatile {
                return Err(ReflectError::unsupported(
                    "volatile Store (fail-closed)".to_string(),
                ));
            }
            if width_of_ty(ty) != Some(width) {
                return Err(ReflectError::unsupported(format!(
                    "Store at type {ty} (Fragment-4 cells are width-U{width} words, \
                     fail-closed)"
                )));
            }
            let a = hw.resolve_cell(*ptr, "Store")?;
            let v = den
                .get(&value.index())
                .cloned()
                .ok_or(ReflectError::UnresolvedOperand(*value))?;
            hw.written.insert(a);
            hw.heap = hwrite(hw.heap.clone(), Expr::nat_lit(a), v);
            Ok(())
        }
        Inst::Load {
            ty,
            ptr,
            volatile,
            align: _,
        } => {
            if *volatile {
                return Err(ReflectError::unsupported(
                    "volatile Load (fail-closed)".to_string(),
                ));
            }
            if width_of_ty(ty) != Some(width) {
                return Err(ReflectError::unsupported(format!(
                    "Load at type {ty} (Fragment-4 cells are width-U{width} words, \
                     fail-closed)"
                )));
            }
            let a = hw.resolve_cell(*ptr, "Load")?;
            if !hw.written.contains(&a) {
                // Uninitialized read: UB in trust-ir's reference semantics
                // (`interpret.rs` reports UndefinedBehavior). Denoting it to
                // `hempty`'s 0 would wrongly CERTIFY a lowering that dropped
                // a store of literal 0 — refuse as a detected wrong emission.
                return Err(ReflectError::WrongEmission(format!(
                    "Load of never-written cell {a} (uninitialized read is UB)"
                )));
            }
            let [r] = node.results.as_slice() else {
                return Err(ReflectError::Malformed(
                    "Load without exactly one result".to_string(),
                ));
            };
            den.insert(r.index(), hread(hw.heap.clone(), Expr::nat_lit(a)));
            Ok(())
        }
        Inst::Release { ptr } => {
            // A Fragment-4 cell is released by `Release` of the allocation's
            // OWN result value — the same shape the emit gate's structural
            // balance check counts. No pointer escapes the fragment and
            // `Retain` is outside it, so the count is 1 here and this
            // `Release` frees the cell. An aliased release (e.g. through a
            // GEP-0 fold) or a release of a value that is not a `HeapAlloc`
            // result is therefore an out-of-fragment refusal HERE, not a false
            // "detected wrong-code emission" at the gate.
            let entry = hw.allocs.get_mut(&ptr.index()).ok_or_else(|| {
                ReflectError::unsupported(
                    "Release pointer is not the allocation's own HeapAlloc result value \
                     (fail-closed)"
                        .to_string(),
                )
            })?;
            // Idempotent liveness kill: dropped/doubled Releases are the emit
            // gate's structural balance check to REFUSE (honesty note 1).
            entry.live = false;
            Ok(())
        }
        // `Dealloc` of a reference-counted `CleanHeap` cell is undefined
        // behaviour (trust-ir SPEC "A reference-counted cell is released by
        // `Release`, never by `Dealloc`"): a lowering that frees a Fragment-4
        // cell with it is a detected wrong emission — REFUSED by the mint
        // gate, never skipped.
        Inst::Dealloc { .. } => Err(ReflectError::WrongEmission(
            "Dealloc of a Fragment-4 CleanHeap cell is undefined behaviour (a \
             reference-counted cell is released by Release)"
                .to_string(),
        )),
        other @ insts!(
            BinOp,
            UnOp,
            Overflow,
            ICmp,
            FCmp,
            Cast,
            Alloca,
            PtrData,
            PtrMetadata,
            PtrFromParts,
            BoxDeref,
            AtomicLoad,
            AtomicStore,
            AtomicRMW,
            CmpXchg,
            Fence,
            Br,
            CondBr,
            Switch,
            Call,
            CallIndirect,
            Return,
            ExtractField,
            InsertField,
            ExtractElement,
            InsertElement,
            Const,
            NullPtr,
            GlobalAddr,
            Undef,
            Assume,
            Assert,
            Unreachable,
            Copy,
            Select,
            SeqMapAddK,
            SeqMapNot,
            SeqMap,
            Borrow,
            BorrowMut,
            EndBorrow,
            Retain,
            IsUnique,
            MemCopy,
            MemSet,
            Drop,
            OpenFrame,
            BindSlot,
            LoadSlot,
            CloseFrame,
            CoroSuspend,
            Invoke,
            InvokeIndirect,
            AssertInvoke,
            CallCannotUnwind,
            CallIndirectCannotUnwind,
            DropInvoke,
            LandingPad,
            Resume,
            DialectOp,
            MakeAggregate,
            ArraySplat,
            MakeClosure,
            TensorContract,
            TensorMap,
            TensorReduce,
            TensorView,
            TensorGather,
            TensorScatter,
        ) => Err(ReflectError::unsupported(fragment2_inst_label(other))),
    }
}

// --- Fragment-5: boxed-scalar (Nat) vocabulary --------------------------------
//
// Fragment-2/3/4 live entirely in machine-scalar `U-w` registers. Fragment-5
// admits the BOXED representation the Clean runtime uses for `Nat` (a tagged
// immediate `< 2^63`, or a heap cell): a `clean_obj*` pointer whose VALUE is an
// unbounded `Nat`. The denotation of a boxed value is still a kernel `Nat`; the
// vocabulary just gains the runtime box/unbox/arith primitives as
// value-transparent (or value-computing) combinators — no new kernel axioms,
// exactly like Fragment-4's `hwrite`/`hread`.
//
// The rows transcribe `crates/clean-runtime/include/clean_runtime.h` +
// `clean_runtime.c` 1:1 (see `f5_vocab_row`). The `Nat` arithmetic ops
// (`l_Nat_*`) are the BIGNUM ops — `Nat.add/mul/sub/div/mod` with Lean's monus
// / `n/0=0` / `n%0=n` conventions — denoted faithfully (no `u64` wrap
// shortcut). The runtime panics above `2^128` rather than wrapping, so the
// value equation is faithful on every completing execution (the fragment's
// standing panic-partiality boundary).
//
// THIS SESSION'S SUBSET (the sound floor): closed, PARAMETER-FREE boxed-Nat
// constants — a `() -> Ptr` function whose body is `Const` / vocabulary calls /
// closed 0-ary helper calls / `Return` (e.g. the `UIntN.size` family:
// `clean_box_uint64 256` via the compiler's `_boxed_const` helper). Parameter-
// carrying rows (box/unbox of params, mixed scalar↔Nat, `Nat` arithmetic over
// params) are the documented ladder — they need the per-parameter SORT plumbing
// that this floor deliberately omits.

/// A denoted SSA value inside a Fragment-5 walk: the kernel `Nat` expression
/// plus a static bound exponent — `Some(b)` claims the value is `< 2^b`
/// (from a scalar carrier width or a literal's magnitude), `None` is an
/// unbounded boxed `Nat`. The bound is what lets a `clean_box` / `clean_unbox`
/// tagged-immediate row prove itself value-faithful (only sound `< 2^63`).
type Den = BTreeMap<u32, (Expr, Option<u32>)>;

/// Depth cap for closed 0-ary helper inlining (the compiler's `_boxed_const`
/// aux decls chain at most one level; deeper fails closed).
const MAX_INLINE_DEPTH: u32 = 4;

/// Tighten a bound to at most `cap` (a value flowing through a `U-cap` carrier
/// is `< 2^cap`).
fn bound_cap(b: Option<u32>, cap: u32) -> Option<u32> {
    Some(b.map_or(cap, |x| x.min(cap)))
}

/// The number of bits to represent the non-negative literal `k` (`k < 2^b`).
fn bitlen_u128(k: u128) -> u32 {
    128 - k.leading_zeros()
}

/// Whether `name` is a Fragment-5 boxed-Nat vocabulary primitive. Only taken
/// when the module function of that name is BODYLESS (a runtime import); an
/// in-module function that shadows one of these names is treated as an ordinary
/// callee/helper instead, never misdenoted.
fn is_f5_vocab_name(name: &str) -> bool {
    matches!(
        name,
        "clean_box"
            | "clean_box_uint32"
            | "clean_box_uint64"
            | "clean_nat_of_u64"
            | "clean_nat_big"
            | "clean_unbox"
            | "clean_unbox_uint32"
            | "clean_unbox_uint64"
            | "l_Nat_add"
            | "l_Nat_mul"
            | "l_Nat_sub"
            | "l_Nat_div"
            | "l_Nat_mod"
    )
}

/// The Fragment-5 emitted-side rows: the value denotation of one call to the
/// BODYLESS runtime extern `name`, given the argument `(denotation, bound)`s.
/// Each row transcribes the documented clean-runtime value semantics 1:1:
///
/// ```text
/// [[clean_box_uint64 x]]  = [[x]]                (Nat carrier of a u64 — exact)
/// [[clean_box_uint32 x]]  = [[x]]                (exact)
/// [[clean_nat_of_u64 x]]  = [[x]]                (exact)
/// [[clean_nat_big lo hi]] = [[lo]] + [[hi]]·2^64  (two-limb literal — exact)
/// [[clean_box x]]         = [[x]]   REQUIRES bound(x) ≤ 63 (tagged immediate)
/// [[clean_unbox p]]       = [[p]]   REQUIRES bound(p) ≤ 63 (tagged immediate)
/// [[clean_unbox_uint64 p]] = [[p]] mod 2^64      (low-64 dispatch — exact)
/// [[clean_unbox_uint32 p]] = [[p]] mod 2^32      (low-32 dispatch — exact)
/// [[l_Nat_add a b]] = Nat.add [[a]] [[b]]        (bignum — exact)
/// [[l_Nat_mul a b]] = Nat.mul [[a]] [[b]]        (bignum — exact)
/// [[l_Nat_sub a b]] = Nat.sub [[a]] [[b]]        (monus both sides — exact)
/// [[l_Nat_div a b]] = Nat.div [[a]] [[b]]        (n/0 = 0 both sides — exact)
/// [[l_Nat_mod a b]] = Nat.mod [[a]] [[b]]        (n%0 = n both sides — exact)
/// ```
///
/// `clean_box`/`clean_unbox` are the raw tagged-immediate pair, faithful ONLY
/// below `2^63`: an operand without a static `< 2^63` bound fails closed.
fn f5_vocab_row(
    name: &str,
    args: &[(Expr, Option<u32>)],
) -> Result<(Expr, Option<u32>), ReflectError> {
    let unary = || -> Result<&(Expr, Option<u32>), ReflectError> {
        let [a] = args else {
            return Err(ReflectError::unsupported(format!(
                "`{name}` called with {} argument(s) (expected 1, fail-closed)",
                args.len()
            )));
        };
        Ok(a)
    };
    let binary = |f: &str| -> Result<(Expr, Option<u32>), ReflectError> {
        let [a, b] = args else {
            return Err(ReflectError::unsupported(format!(
                "`{name}` called with {} argument(s) (expected 2, fail-closed)",
                args.len()
            )));
        };
        Ok((nat_app2(f, a.0.clone(), b.0.clone()), None))
    };
    match name {
        "clean_box_uint64" | "clean_nat_of_u64" => {
            let (e, b) = unary()?;
            Ok((e.clone(), bound_cap(*b, 64)))
        }
        "clean_box_uint32" => {
            let (e, b) = unary()?;
            Ok((e.clone(), bound_cap(*b, 32)))
        }
        "clean_box" | "clean_unbox" => {
            let (e, b) = unary()?;
            match b {
                Some(bb) if *bb <= 63 => Ok((e.clone(), Some(*bb))),
                _ => Err(ReflectError::unsupported(format!(
                    "`{name}` of a value without a static < 2^63 bound (the raw \
                     tagged-immediate box/unbox is only value-faithful below 2^63, \
                     fail-closed)"
                ))),
            }
        }
        "clean_unbox_uint64" => {
            let (e, b) = unary()?;
            match b {
                Some(bb) if *bb <= 64 => Ok((e.clone(), Some(*bb))),
                _ => Ok((wrap(e.clone(), &modulus(64)), Some(64))),
            }
        }
        "clean_unbox_uint32" => {
            let (e, b) = unary()?;
            match b {
                Some(bb) if *bb <= 32 => Ok((e.clone(), Some(*bb))),
                _ => Ok((wrap(e.clone(), &modulus(32)), Some(32))),
            }
        }
        "clean_nat_big" => {
            let [lo, hi] = args else {
                return Err(ReflectError::unsupported(format!(
                    "`clean_nat_big` called with {} argument(s) (expected 2, fail-closed)",
                    args.len()
                )));
            };
            let hi_scaled = nat_app2("Nat.mul", hi.0.clone(), Expr::nat_lit_u128(1u128 << 64));
            Ok((nat_app2("Nat.add", lo.0.clone(), hi_scaled), None))
        }
        "l_Nat_add" => binary("Nat.add"),
        "l_Nat_mul" => binary("Nat.mul"),
        "l_Nat_sub" => binary("Nat.sub"),
        "l_Nat_div" => binary("Nat.div"),
        "l_Nat_mod" => binary("Nat.mod"),
        other => Err(ReflectError::unsupported(format!(
            "`{other}` is not a Fragment-5 vocabulary primitive (fail-closed)"
        ))),
    }
}

/// Record a `Const` node into a Fragment-5 walk: an unsigned integer constant
/// `k` at type `U-w` denotes to the `Nat` literal `k`, bounded by its exact
/// magnitude (`k < 2^bitlen(k)`, itself `≤ w`). Fail-closed on non-Int / signed
/// / negative constants.
fn f5_eval_const(
    node: &trust_ir::InstrNode,
    ty: &Ty,
    value: &Constant,
    den: &mut Den,
) -> Result<(), ReflectError> {
    let Constant::Int(k) = value else {
        return Err(ReflectError::unsupported(
            "non-Int constant (Fragment-5 constants are unsigned integers, fail-closed)"
                .to_string(),
        ));
    };
    let w = width_of_ty(ty).ok_or_else(|| {
        ReflectError::unsupported(format!(
            "Const at type {ty} (Fragment-5 constants are U8/U16/U32/U64, fail-closed)"
        ))
    })?;
    if *k < 0 {
        return Err(ReflectError::unsupported(
            "negative Const (fail-closed)".to_string(),
        ));
    }
    #[allow(clippy::cast_sign_loss)]
    let kk = *k as u128;
    if w < 64 && kk >= (1u128 << w) {
        return Err(ReflectError::unsupported(format!(
            "Const {kk} out of range for U{w} (fail-closed)"
        )));
    }
    let [r] = node.results.as_slice() else {
        return Err(ReflectError::Malformed(
            "Const without exactly one result".to_string(),
        ));
    };
    let bound = bitlen_u128(kk).min(w);
    let lit = if kk <= u128::from(u64::MAX) {
        #[allow(clippy::cast_possible_truncation)]
        Expr::nat_lit(kk as u64)
    } else {
        Expr::nat_lit_u128(kk)
    };
    den.insert(r.index(), (lit, Some(bound)));
    Ok(())
}

/// Denote a closed, PARAMETER-FREE, single-block helper function to a `Nat`
/// value denotation (`(Expr, bound)`) — the Fragment-5 treatment of the
/// compiler-generated `_boxed_const` aux decls, which have no kernel definition
/// and can never be pinned callees. Inlining IS function unfolding in the value
/// model: the call denotes to the callee's own body denotation. Fail-closed on
/// anything but `Const` / `Copy` / `Retain` / `Release` / vocabulary calls /
/// nested closed 0-ary calls (depth-capped). Rejects `Cast` (value-changing).
fn denote_closed_zeroary(
    module: &Module,
    func: &Function,
    depth: u32,
) -> Result<(Expr, Option<u32>), ReflectError> {
    if depth == 0 {
        return Err(ReflectError::unsupported(
            "closed helper inlining exceeded the depth cap (fail-closed)".to_string(),
        ));
    }
    let func_ty = module.func_types.get(func.ty.as_usize()).ok_or_else(|| {
        ReflectError::Malformed(format!("function {} has a dangling FuncTyId", func.name))
    })?;
    if !func_ty.params.is_empty() {
        return Err(ReflectError::unsupported(
            "closed helper inlining requires a 0-ary callee (fail-closed)".to_string(),
        ));
    }
    let [block] = func.blocks.as_slice() else {
        return Err(ReflectError::unsupported(
            "closed helper inlining requires a single-block callee (fail-closed)".to_string(),
        ));
    };
    if !block.params.is_empty() {
        return Err(ReflectError::Malformed(format!(
            "0-ary function {} has entry block params",
            func.name
        )));
    }
    let (term, prefix) = block.body.split_last().ok_or_else(|| {
        ReflectError::Malformed(format!(
            "function {} entry block has no terminator",
            func.name
        ))
    })?;
    let mut den: Den = BTreeMap::new();
    for node in prefix {
        match &node.inst {
            Inst::Const { ty, value } => f5_eval_const(node, ty, value, &mut den)?,
            Inst::Copy { operand, .. } => {
                let d = den
                    .get(&operand.index())
                    .cloned()
                    .ok_or(ReflectError::UnresolvedOperand(*operand))?;
                let [r] = node.results.as_slice() else {
                    return Err(ReflectError::Malformed(
                        "Copy without exactly one result".to_string(),
                    ));
                };
                den.insert(r.index(), d);
            }
            // Value-invisible; their ownership is `f5_ownership_balance`'s.
            Inst::Retain { .. } | Inst::Release { .. } => {}
            Inst::Call { callee, args } => {
                let f = module
                    .functions
                    .iter()
                    .find(|f| f.id == *callee)
                    .ok_or_else(|| {
                        ReflectError::Malformed(format!("Call targets missing function {callee:?}"))
                    })?;
                let mut arg_dens = Vec::with_capacity(args.len());
                for a in args {
                    arg_dens.push(
                        den.get(&a.index())
                            .cloned()
                            .ok_or(ReflectError::UnresolvedOperand(*a))?,
                    );
                }
                let rd = if f.blocks.is_empty() && is_f5_vocab_name(&f.name) {
                    f5_vocab_row(&f.name, &arg_dens)?
                } else if !f.blocks.is_empty() && arg_dens.is_empty() {
                    denote_closed_zeroary(module, f, depth - 1)?
                } else {
                    return Err(ReflectError::unsupported(format!(
                        "closed helper inlining hit a non-vocabulary call to `{}` \
                         (fail-closed)",
                        f.name
                    )));
                };
                let [r] = node.results.as_slice() else {
                    return Err(ReflectError::unsupported(
                        "Call without exactly one result (fail-closed)".to_string(),
                    ));
                };
                den.insert(r.index(), rd);
            }
            other @ insts!(
                BinOp,
                UnOp,
                Overflow,
                ICmp,
                FCmp,
                Cast,
                Load,
                Store,
                Alloca,
                HeapAlloc,
                GEP,
                PtrData,
                PtrMetadata,
                PtrFromParts,
                BoxDeref,
                AtomicLoad,
                AtomicStore,
                AtomicRMW,
                CmpXchg,
                Fence,
                Br,
                CondBr,
                Switch,
                CallIndirect,
                Return,
                ExtractField,
                InsertField,
                ExtractElement,
                InsertElement,
                NullPtr,
                GlobalAddr,
                Undef,
                Assume,
                Assert,
                Unreachable,
                Select,
                SeqMapAddK,
                SeqMapNot,
                SeqMap,
                Borrow,
                BorrowMut,
                EndBorrow,
                IsUnique,
                Dealloc,
                MemCopy,
                MemSet,
                Drop,
                OpenFrame,
                BindSlot,
                LoadSlot,
                CloseFrame,
                CoroSuspend,
                Invoke,
                InvokeIndirect,
                AssertInvoke,
                CallCannotUnwind,
                CallIndirectCannotUnwind,
                DropInvoke,
                LandingPad,
                Resume,
                DialectOp,
                MakeAggregate,
                ArraySplat,
                MakeClosure,
                TensorContract,
                TensorMap,
                TensorReduce,
                TensorView,
                TensorGather,
                TensorScatter,
            ) => {
                return Err(ReflectError::unsupported(format!(
                    "closed helper inlining: {}",
                    fragment2_inst_label(other)
                )));
            }
        }
    }
    let Inst::Return { values } = &term.inst else {
        return Err(ReflectError::unsupported(
            "closed helper does not end in Return (fail-closed)".to_string(),
        ));
    };
    let [v] = values.as_slice() else {
        return Err(ReflectError::unsupported(
            "closed helper with a multi-value return (fail-closed)".to_string(),
        ));
    };
    den.get(&v.index())
        .cloned()
        .ok_or(ReflectError::UnresolvedOperand(*v))
}

// --- Fragment-5 ownership: the per-reference balance -------------------------

/// Whether the Fragment-5 runtime row `name` GIVES UP each boxed reference it
/// is passed: Clean's `l_Nat_*` shims (`clean-cli`'s `native_build.rs`) call
/// `clean_nat_*`, which read both operands and then `clean_dec` both
/// (`clean_runtime.c`) — the Perceus all-owned ABI. Checker spec transcribed
/// from those two files; nothing checks the shims against it.
fn f5_consumes_ptr_args(name: &str) -> bool {
    matches!(
        name,
        "l_Nat_add" | "l_Nat_sub" | "l_Nat_mul" | "l_Nat_div" | "l_Nat_mod"
    )
}

/// Whether the Fragment-5 runtime row `name` only READS a boxed reference it
/// is passed: `clean_unbox` / `clean_unbox_uint32` / `clean_unbox_uint64`
/// (`clean_runtime.h`, `runtime_extern.c`) decode their argument and never
/// dec it.
fn f5_borrows_ptr_arg(name: &str) -> bool {
    matches!(
        name,
        "clean_unbox" | "clean_unbox_uint32" | "clean_unbox_uint64"
    )
}

/// The owned boxed references of ONE Fragment-5 body: each `Ptr` result of a
/// call is a reference at count 1, and a `Copy` of it names the same one.
struct F5Ledger<'f> {
    func: &'f str,
    /// SSA value -> index into `refs` (a `Copy` maps to its operand's index).
    names: BTreeMap<u32, usize>,
    /// Per reference: the value that created it and its current count.
    refs: Vec<(u32, u64)>,
}

impl<'f> F5Ledger<'f> {
    fn new(func: &'f str) -> Self {
        F5Ledger {
            func,
            names: BTreeMap::new(),
            refs: Vec::new(),
        }
    }

    fn reference(&self, v: ValueId) -> Option<usize> {
        self.names.get(&v.index()).copied()
    }

    /// A call's `Ptr` result: a new reference the body owns, at count 1.
    fn own(&mut self, v: ValueId) {
        self.names.insert(v.index(), self.refs.len());
        self.refs.push((v.index(), 1));
    }

    /// The reference `v` names, or the fail-closed skip for an RC operation
    /// on a value that is not one (outside the fragment, never a refusal).
    fn rc_operand(&self, v: ValueId, op: &str) -> Result<usize, ReflectError> {
        self.reference(v).ok_or_else(|| {
            ReflectError::unsupported(format!(
                "Fragment-5 ownership: `{op}` of %{} in `{}`, which is not a boxed reference \
                 a call returned (fail-closed)",
                v.index(),
                self.func
            ))
        })
    }

    /// Every operation needs a live reference: count >= 1.
    fn live(&self, r: usize, op: &str) -> Result<(), ReflectError> {
        let (origin, count) = self.refs[r];
        if count == 0 {
            return Err(ReflectError::WrongEmission(format!(
                "Fragment-5 ownership balance in `{}`: {op} of the reference %{origin} after its \
                 last reference is gone (use after free / count underflow)",
                self.func
            )));
        }
        Ok(())
    }

    fn retain(&mut self, r: usize) -> Result<(), ReflectError> {
        self.live(r, "a Retain")?;
        self.refs[r].1 += 1;
        Ok(())
    }

    fn give_up(&mut self, r: usize, op: &str) -> Result<(), ReflectError> {
        self.live(r, op)?;
        self.refs[r].1 -= 1;
        Ok(())
    }

    /// The body must end having given up every reference it owned.
    fn finish(self) -> Result<(), ReflectError> {
        match self.refs.iter().find(|(_, count)| *count > 0) {
            None => Ok(()),
            Some((origin, count)) => Err(ReflectError::WrongEmission(format!(
                "Fragment-5 ownership balance in `{}`: the reference %{origin} is still held at \
                 count {count} when the body returns (a leak)",
                self.func
            ))),
        }
    }
}

/// The Fragment-5 OWNERSHIP BALANCE (trust-ir SPEC "A reference-counted cell
/// is released by `Release`, never by `Dealloc`", clause 4) over a body
/// [`denote_closed_zeroary`] already admitted. The value denotation cannot see
/// reference counting — `Retain` / `Release` and the runtime's argument
/// consumption are value-invisible — so this separate structural pass checks
/// it, on every admitted body, whether or not the kernel ever judges its
/// equation:
///
/// * every `Ptr` result of a call is an owned reference at count 1; a `Copy`
///   names the same reference;
/// * `Retain` adds one; a `Release`, an argument of an `l_Nat_*` row
///   ([`f5_consumes_ptr_args`]) and the `Return` each give one up; an argument
///   of a `clean_unbox*` row ([`f5_borrows_ptr_arg`]) needs the reference
///   live and gives nothing up;
/// * each operation needs count >= 1, and the body must end at 0 for every
///   reference; each inlined 0-ary helper is held to this on its own body,
///   and its `Ptr` call result starts at count 1 in the caller.
///
/// A violation — a use or give-up after the last reference is gone (use
/// after free, count underflow), or a reference still held at the end (a
/// leak) — is [`ReflectError::WrongEmission`]: the minter REFUSES it as a
/// detected miscompile. A `Retain` / `Release` of a value that is not such a
/// reference, or a reference handed to a row whose convention is not
/// modelled, is outside the fragment ([`ReflectError::Unsupported`], a skip).
fn f5_ownership_balance(module: &Module, func: &Function, depth: u32) -> Result<(), ReflectError> {
    if depth == 0 {
        return Err(ReflectError::unsupported(
            "Fragment-5 ownership: helper inlining exceeded the depth cap (fail-closed)"
                .to_string(),
        ));
    }
    let [block] = func.blocks.as_slice() else {
        return Err(ReflectError::unsupported(
            "Fragment-5 ownership: a single-block body is required (fail-closed)".to_string(),
        ));
    };
    let (term, prefix) = block.body.split_last().ok_or_else(|| {
        ReflectError::Malformed(format!(
            "function {} entry block has no terminator",
            func.name
        ))
    })?;
    let mut ledger = F5Ledger::new(&func.name);
    for node in prefix {
        match &node.inst {
            // A scalar constant is not a reference.
            Inst::Const { .. } => {}
            Inst::Copy { operand, .. } => {
                let [r] = node.results.as_slice() else {
                    return Err(ReflectError::Malformed(
                        "Copy without exactly one result".to_string(),
                    ));
                };
                if let Some(reference) = ledger.reference(*operand) {
                    ledger.names.insert(r.index(), reference);
                }
            }
            Inst::Retain { ptr } => {
                let reference = ledger.rc_operand(*ptr, "Retain")?;
                ledger.retain(reference)?;
            }
            Inst::Release { ptr } => {
                let reference = ledger.rc_operand(*ptr, "Release")?;
                ledger.give_up(reference, "a Release")?;
            }
            Inst::Call { callee, args } => {
                let f = module
                    .functions
                    .iter()
                    .find(|f| f.id == *callee)
                    .ok_or_else(|| {
                        ReflectError::Malformed(format!("Call targets missing function {callee:?}"))
                    })?;
                if f.blocks.is_empty() && is_f5_vocab_name(&f.name) {
                    for a in args {
                        let Some(reference) = ledger.reference(*a) else {
                            continue;
                        };
                        if f5_consumes_ptr_args(&f.name) {
                            ledger.give_up(reference, &format!("an argument of `{}`", f.name))?;
                        } else if f5_borrows_ptr_arg(&f.name) {
                            ledger.live(reference, &format!("an argument of `{}`", f.name))?;
                        } else {
                            return Err(ReflectError::unsupported(format!(
                                "Fragment-5 ownership: a boxed reference passed to `{}`, whose \
                                 ownership convention is not modelled (fail-closed)",
                                f.name
                            )));
                        }
                    }
                } else if !f.blocks.is_empty() && args.is_empty() {
                    f5_ownership_balance(module, f, depth - 1)?;
                } else {
                    return Err(ReflectError::unsupported(format!(
                        "Fragment-5 ownership: a call to `{}` outside the vocabulary \
                         (fail-closed)",
                        f.name
                    )));
                }
                let returns_ptr = module
                    .func_types
                    .get(f.ty.as_usize())
                    .is_some_and(|ft| ft.returns.as_slice() == [Ty::Ptr]);
                if returns_ptr {
                    let [r] = node.results.as_slice() else {
                        return Err(ReflectError::unsupported(
                            "Call without exactly one result (fail-closed)".to_string(),
                        ));
                    };
                    ledger.own(*r);
                }
            }
            other @ insts!(
                BinOp,
                UnOp,
                Overflow,
                ICmp,
                FCmp,
                Cast,
                Load,
                Store,
                Alloca,
                HeapAlloc,
                GEP,
                PtrData,
                PtrMetadata,
                PtrFromParts,
                BoxDeref,
                AtomicLoad,
                AtomicStore,
                AtomicRMW,
                CmpXchg,
                Fence,
                Br,
                CondBr,
                Switch,
                CallIndirect,
                Return,
                ExtractField,
                InsertField,
                ExtractElement,
                InsertElement,
                NullPtr,
                GlobalAddr,
                Undef,
                Assume,
                Assert,
                Unreachable,
                Select,
                SeqMapAddK,
                SeqMapNot,
                SeqMap,
                Borrow,
                BorrowMut,
                EndBorrow,
                IsUnique,
                Dealloc,
                MemCopy,
                MemSet,
                Drop,
                OpenFrame,
                BindSlot,
                LoadSlot,
                CloseFrame,
                CoroSuspend,
                Invoke,
                InvokeIndirect,
                AssertInvoke,
                CallCannotUnwind,
                CallIndirectCannotUnwind,
                DropInvoke,
                LandingPad,
                Resume,
                DialectOp,
                MakeAggregate,
                ArraySplat,
                MakeClosure,
                TensorContract,
                TensorMap,
                TensorReduce,
                TensorView,
                TensorGather,
                TensorScatter,
            ) => {
                return Err(ReflectError::unsupported(format!(
                    "Fragment-5 ownership: {}",
                    fragment2_inst_label(other)
                )));
            }
        }
    }
    let Inst::Return { values } = &term.inst else {
        return Err(ReflectError::unsupported(
            "Fragment-5 ownership: the body does not end in Return (fail-closed)".to_string(),
        ));
    };
    for v in values {
        if let Some(reference) = ledger.reference(*v) {
            ledger.give_up(reference, "the Return")?;
        }
    }
    ledger.finish()
}

// --- Emitted side: trust-ir Function -> denotation ---------------------------

/// Denote an EMITTED trust-ir function into the shared Fragment-2 vocabulary.
///
/// Fail-closed: any function outside the fragment (multiple blocks, calls,
/// memory, non-uniform widths, non-Int constants, extra results, …) is
/// [`ReflectError::Unsupported`] with an auditable label — never a wrong or
/// partial denotation.
///
/// # Errors
///
/// [`ReflectError::Unsupported`] outside the fragment;
/// [`ReflectError::Malformed`] when the module/function is structurally
/// inconsistent (dangling type ids, unbound operands, missing terminator).
pub fn denote_function(module: &Module, func: &Function) -> Result<TvDenotation, ReflectError> {
    let func_ty = module.func_types.get(func.ty.as_usize()).ok_or_else(|| {
        ReflectError::Malformed(format!("function {} has a dangling FuncTyId", func.name))
    })?;

    // One uniform width, read off the (single) return type.
    let [ret_ty] = func_ty.returns.as_slice() else {
        return Err(ReflectError::unsupported(
            "function without exactly one return value (out of fragment, fail-closed)",
        ));
    };

    // Fragment-5 (this session's sound floor): a PARAMETER-FREE boxed-`Nat`
    // constant — `() -> Ptr` built from the boxed-scalar vocabulary. Delegates
    // to the closed-inlining walker; the denotation is a closed `Nat`, arity 0,
    // no callees. `width` is nominal 64 (there is no scalar position).
    if func_ty.params.is_empty() && matches!(ret_ty, Ty::Ptr) {
        let (body, _bound) = denote_closed_zeroary(module, func, MAX_INLINE_DEPTH)?;
        // Reference counting is invisible to the value denotation above, so
        // its discipline is checked here, on every admitted body — kernel-
        // judged later or not (SPEC clause 4, `f5_ownership_balance`).
        f5_ownership_balance(module, func, MAX_INLINE_DEPTH)?;
        return Ok(TvDenotation {
            arity: 0,
            width: 64,
            body,
            callees: Vec::new(),
        });
    }

    let width = width_of_ty(ret_ty).ok_or_else(|| {
        ReflectError::unsupported(format!(
            "return type {ret_ty} (fragment is U8/U16/U32/U64 only, fail-closed)"
        ))
    })?;
    for p in &func_ty.params {
        if width_of_ty(p) != Some(width) {
            return Err(ReflectError::unsupported(format!(
                "parameter type {p} (fragment requires every param at the uniform \
                 width U{width}, fail-closed)"
            )));
        }
    }

    let entry = func
        .blocks
        .iter()
        .find(|b| b.id == func.entry)
        .ok_or_else(|| {
            ReflectError::Malformed(format!("function {} has no entry block", func.name))
        })?;
    if entry.params.len() != func_ty.params.len() {
        return Err(ReflectError::Malformed(format!(
            "function {}: entry block params disagree with the signature",
            func.name
        )));
    }

    let arity = entry.params.len();
    let m = modulus(width);

    // SSA value -> denotation. Params are the innermost `arity` binders in
    // declaration order: param i |-> bvar(arity - 1 - i). The entry block's map
    // is threaded into the branch arms (which the entry block dominates), so an
    // arm may reference any entry-defined value.
    let mut den: BTreeMap<u32, Expr> = BTreeMap::new();
    for (i, (v, pty)) in entry.params.iter().enumerate() {
        if width_of_ty(pty) != Some(width) {
            return Err(ReflectError::unsupported(format!(
                "block param type {pty} at uniform width U{width} (fail-closed)"
            )));
        }
        den.insert(v.index(), Expr::bvar((arity - 1 - i) as u32));
    }

    // The terminator determines the shape; the prefix is processed with the
    // node set that shape allows (calls only in the single-block Fragment-2/3b
    // case; a comparison only in the Fragment-3a CondBr case).
    let (term, prefix) = entry
        .body
        .split_last()
        .ok_or_else(|| ReflectError::Malformed("entry block has no terminator".to_string()))?;

    // Fragment-4: the per-function BLOCK constant (deterministic; derived
    // before walking so every segment shares it).
    let block_constant = heap_block_constant(module, func)?;

    match &term.inst {
        Inst::Return { values } => {
            // Fragment-2 (+ Fragment-3b calls, + Fragment-4 heap ops): a
            // single straight-line block threading one heap term.
            if func.blocks.len() != 1 {
                return Err(ReflectError::unsupported(
                    "multi-block function whose entry returns directly (out of fragment, \
                     fail-closed)",
                ));
            }
            // Pre-scan the block for callees so a `Call` can denote to its
            // pinned symbol (callees are OUTER binders; params keep bvar(i)).
            let (callees, symbol_of) = scan_callees(module, entry, arity)?;
            let call_ctx = (module, &symbol_of);
            let mut hw = HeapWalk::new(module, block_constant);
            for node in prefix {
                eval_value_node(
                    node,
                    width,
                    &m,
                    &mut den,
                    false,
                    Some(call_ctx),
                    Some(&mut hw),
                )?;
            }
            let [v] = values.as_slice() else {
                return Err(ReflectError::unsupported(
                    "multi-value return (out of fragment, fail-closed)",
                ));
            };
            let body = den
                .get(&v.index())
                .cloned()
                .ok_or(ReflectError::UnresolvedOperand(*v))?;
            Ok(TvDenotation {
                arity,
                width,
                body,
                callees,
            })
        }
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            // Fragment-3a: entry `CondBr` diamond, two return paths (call-free).
            if func.blocks.len() != 3 {
                return Err(ReflectError::unsupported(format!(
                    "CondBr function with {} block(s) (Fragment-3a is exactly entry + two \
                     return arms, fail-closed)",
                    func.blocks.len()
                )));
            }
            if !then_args.is_empty() || !else_args.is_empty() {
                return Err(ReflectError::unsupported(
                    "CondBr passes block arguments on a branch edge (Fragment-3a arms take \
                     no params — they read the dominating entry values directly, fail-closed)",
                ));
            }
            // Heap ops must stay within one arm (module docs), so the entry
            // prefix walks with NO heap context — a heap op here fails closed.
            for node in prefix {
                eval_value_node(node, width, &m, &mut den, true, None, None)?;
            }
            let c = den
                .get(&cond.index())
                .cloned()
                .ok_or(ReflectError::UnresolvedOperand(*cond))?;
            let then_body =
                denote_arm(module, func, *then_target, width, &m, &den, block_constant)?;
            let else_body =
                denote_arm(module, func, *else_target, width, &m, &den, block_constant)?;
            Ok(TvDenotation {
                arity,
                width,
                body: ite_nat(c, then_body, else_body),
                callees: Vec::new(),
            })
        }
        other @ insts!(
            BinOp,
            UnOp,
            Overflow,
            ICmp,
            FCmp,
            Cast,
            Load,
            Store,
            Alloca,
            HeapAlloc,
            GEP,
            PtrData,
            PtrMetadata,
            PtrFromParts,
            BoxDeref,
            AtomicLoad,
            AtomicStore,
            AtomicRMW,
            CmpXchg,
            Fence,
            Br,
            Switch,
            Call,
            CallIndirect,
            ExtractField,
            InsertField,
            ExtractElement,
            InsertElement,
            Const,
            NullPtr,
            GlobalAddr,
            Undef,
            Assume,
            Assert,
            Unreachable,
            Copy,
            Select,
            SeqMapAddK,
            SeqMapNot,
            SeqMap,
            Borrow,
            BorrowMut,
            EndBorrow,
            Retain,
            Release,
            IsUnique,
            Dealloc,
            MemCopy,
            MemSet,
            Drop,
            OpenFrame,
            BindSlot,
            LoadSlot,
            CloseFrame,
            CoroSuspend,
            Invoke,
            InvokeIndirect,
            AssertInvoke,
            CallCannotUnwind,
            CallIndirectCannotUnwind,
            DropInvoke,
            LandingPad,
            Resume,
            DialectOp,
            MakeAggregate,
            ArraySplat,
            MakeClosure,
            TensorContract,
            TensorMap,
            TensorReduce,
            TensorView,
            TensorGather,
            TensorScatter,
        ) => Err(ReflectError::unsupported(fragment2_inst_label(other))),
    }
}

/// Fold ONE value-producing node into the SSA denotation map: `Const`/`BinOp`
/// always; `ICmp` when `allow_icmp`; `Call` when a call context
/// `(module, name -> symbol bvar)` is supplied; heap ops (Fragment-4) when a
/// [`HeapWalk`] is supplied. Fail-closed on anything else.
#[allow(clippy::too_many_arguments)]
fn eval_value_node(
    node: &trust_ir::InstrNode,
    width: u32,
    m: &Expr,
    den: &mut BTreeMap<u32, Expr>,
    allow_icmp: bool,
    call_ctx: Option<(&Module, &BTreeMap<String, u32>)>,
    heap: Option<&mut HeapWalk<'_>>,
) -> Result<(), ReflectError> {
    match &node.inst {
        // `Dealloc` stays in this group so the walker can refuse it BY NAME as
        // a wrong emission (undefined behaviour on a reference-counted cell);
        // dropped from it, it would fall to the generic out-of-fragment
        // refusal below — an `Unsupported` the mint gate SKIPS rather than
        // refuses.
        Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::Store { .. }
        | Inst::Load { .. }
        | Inst::Release { .. }
        | Inst::Dealloc { .. } => {
            let Some(hw) = heap else {
                return Err(ReflectError::unsupported(
                    "heap op outside a heap-capable segment (Fragment-4 heap ops live in \
                     the single straight-line block or within one CondBr arm, fail-closed)"
                        .to_string(),
                ));
            };
            eval_heap_node(node, width, den, hw)
        }
        Inst::Call { callee, args } if call_ctx.is_some() => {
            let (module, symbol_of) = call_ctx.unwrap();
            let f = module
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .ok_or_else(|| {
                    ReflectError::Malformed(format!("Call targets missing function {callee:?}"))
                })?;
            let sym = *symbol_of.get(&f.name).ok_or_else(|| {
                ReflectError::Malformed(format!(
                    "callee `{}` was not registered by the callee pre-scan",
                    f.name
                ))
            })?;
            let mut arg_dens = Vec::with_capacity(args.len());
            for a in args {
                arg_dens.push(
                    den.get(&a.index())
                        .cloned()
                        .ok_or(ReflectError::UnresolvedOperand(*a))?,
                );
            }
            let [r] = node.results.as_slice() else {
                return Err(ReflectError::unsupported(
                    "Call without exactly one result (out of Fragment-3b, fail-closed)",
                ));
            };
            den.insert(r.index(), Expr::apps(Expr::bvar(sym), arg_dens));
            Ok(())
        }
        Inst::Const { ty, value } => {
            let Constant::Int(k) = value else {
                return Err(ReflectError::unsupported(
                    "non-Int constant (out of fragment, fail-closed)",
                ));
            };
            let [r] = node.results.as_slice() else {
                return Err(ReflectError::Malformed(
                    "Const without exactly one result".to_string(),
                ));
            };
            let const_width = if width_of_ty(ty) == Some(width) {
                width
            } else if let (Some(_), Some(w)) = (&heap, width_of_ty(ty)) {
                // Fragment-4: an unsigned constant at ANOTHER width is a
                // closed GEP index only — it gets NO value denotation, so
                // using it in arithmetic stays out of fragment.
                w
            } else {
                return Err(ReflectError::unsupported(format!(
                    "Const at type {ty} (fragment width is U{width}, fail-closed)"
                )));
            };
            let max = 1i128 << const_width;
            if *k < 0 || *k >= max {
                return Err(ReflectError::unsupported(format!(
                    "integer constant {k} outside [0, 2^{const_width}) (fail-closed)"
                )));
            }
            #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
            let lit = *k as u64;
            if const_width == width {
                den.insert(r.index(), Expr::nat_lit(lit));
            }
            if let Some(hw) = heap {
                hw.concrete.insert(r.index(), lit);
            }
            Ok(())
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            if width_of_ty(ty) != Some(width) {
                return Err(ReflectError::unsupported(format!(
                    "BinOp at type {ty} (fragment width is U{width}, fail-closed)"
                )));
            }
            let a = den
                .get(&lhs.index())
                .cloned()
                .ok_or(ReflectError::UnresolvedOperand(*lhs))?;
            let b = den
                .get(&rhs.index())
                .cloned()
                .ok_or(ReflectError::UnresolvedOperand(*rhs))?;
            let e = denote_binop(*op, a, b, m)?;
            let [r] = node.results.as_slice() else {
                return Err(ReflectError::Malformed(
                    "BinOp without exactly one result".to_string(),
                ));
            };
            den.insert(r.index(), e);
            Ok(())
        }
        Inst::ICmp { op, ty, lhs, rhs } if allow_icmp => {
            if width_of_ty(ty) != Some(width) {
                return Err(ReflectError::unsupported(format!(
                    "ICmp at type {ty} (fragment width is U{width}, fail-closed)"
                )));
            }
            let a = den
                .get(&lhs.index())
                .cloned()
                .ok_or(ReflectError::UnresolvedOperand(*lhs))?;
            let b = den
                .get(&rhs.index())
                .cloned()
                .ok_or(ReflectError::UnresolvedOperand(*rhs))?;
            let e = denote_icmp(*op, a, b)?;
            let [r] = node.results.as_slice() else {
                return Err(ReflectError::Malformed(
                    "ICmp without exactly one result".to_string(),
                ));
            };
            den.insert(r.index(), e);
            Ok(())
        }
        // `Call`/`ICmp` are listed as well: their arms above are GUARDED, and a
        // guard that does not hold falls through to this refusal.
        other @ insts!(
            UnOp,
            Overflow,
            ICmp,
            FCmp,
            Cast,
            Alloca,
            PtrData,
            PtrMetadata,
            PtrFromParts,
            BoxDeref,
            AtomicLoad,
            AtomicStore,
            AtomicRMW,
            CmpXchg,
            Fence,
            Br,
            CondBr,
            Switch,
            Call,
            CallIndirect,
            Return,
            ExtractField,
            InsertField,
            ExtractElement,
            InsertElement,
            NullPtr,
            GlobalAddr,
            Undef,
            Assume,
            Assert,
            Unreachable,
            Copy,
            Select,
            SeqMapAddK,
            SeqMapNot,
            SeqMap,
            Borrow,
            BorrowMut,
            EndBorrow,
            Retain,
            IsUnique,
            MemCopy,
            MemSet,
            Drop,
            OpenFrame,
            BindSlot,
            LoadSlot,
            CloseFrame,
            CoroSuspend,
            Invoke,
            InvokeIndirect,
            AssertInvoke,
            CallCannotUnwind,
            CallIndirectCannotUnwind,
            DropInvoke,
            LandingPad,
            Resume,
            DialectOp,
            MakeAggregate,
            ArraySplat,
            MakeClosure,
            TensorContract,
            TensorMap,
            TensorReduce,
            TensorView,
            TensorGather,
            TensorScatter,
        ) => Err(ReflectError::unsupported(fragment2_inst_label(other))),
    }
}

/// Denote a Fragment-3a branch arm: a block reached by the entry `CondBr` that
/// takes no params, runs a Fragment-2 arithmetic prefix (reading the entry's
/// dominating values via `entry_den`), and ends in a single-value `Return`.
/// Each arm threads its OWN fresh heap (Fragment-4: heap use stays within one
/// arm), sharing the per-function `BLOCK` constant.
#[allow(clippy::too_many_arguments)]
fn denote_arm(
    module: &Module,
    func: &Function,
    target: BlockId,
    width: u32,
    m: &Expr,
    entry_den: &BTreeMap<u32, Expr>,
    block_constant: u64,
) -> Result<Expr, ReflectError> {
    let block = func.blocks.iter().find(|b| b.id == target).ok_or_else(|| {
        ReflectError::Malformed(format!("CondBr targets missing block {target:?}"))
    })?;
    if !block.params.is_empty() {
        return Err(ReflectError::unsupported(
            "branch arm block has parameters (Fragment-3a arms are param-free, fail-closed)",
        ));
    }
    let mut den = entry_den.clone();
    let (term, prefix) = block
        .body
        .split_last()
        .ok_or_else(|| ReflectError::Malformed("branch arm block has no terminator".to_string()))?;
    let mut hw = HeapWalk::new(module, block_constant);
    for node in prefix {
        eval_value_node(node, width, m, &mut den, false, None, Some(&mut hw))?;
    }
    let Inst::Return { values } = &term.inst else {
        return Err(ReflectError::unsupported(
            "branch arm does not end in Return (Fragment-3a arms are two return paths, \
             fail-closed)",
        ));
    };
    let [v] = values.as_slice() else {
        return Err(ReflectError::unsupported(
            "multi-value return in branch arm (out of fragment, fail-closed)",
        ));
    };
    den.get(&v.index())
        .cloned()
        .ok_or(ReflectError::UnresolvedOperand(*v))
}

/// A short, auditable label for an instruction outside Fragment-2 (mirrors
/// Fragment-1's `inst_label` convention).
fn fragment2_inst_label(inst: &Inst) -> String {
    let label = match inst {
        Inst::CallIndirect { .. } => "CallIndirect (Fragment-3b is direct calls only)",
        Inst::Call { .. } => "Call outside the single-block Fragment-3b (e.g. inside a branch arm)",
        Inst::Alloca { .. } => "stack Alloca (Fragment-4 heap is CleanHeap HeapAlloc only)",
        Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::Release { .. }
        | Inst::Dealloc { .. } => "heap op outside a heap-capable straight-line segment",
        Inst::Br { .. } | Inst::Switch { .. } => "unstructured branch (only a CondBr diamond)",
        Inst::CondBr { .. } => "CondBr outside the entry terminator position",
        Inst::ICmp { .. } => "ICmp outside a CondBr condition position",
        Inst::Cast { .. } => "Cast (single-width fragment)",
        Inst::Return { .. } => "Return before the end of the block",
        Inst::Const { .. } | Inst::BinOp { .. } => {
            "trailing Const/BinOp with no terminator after it"
        }
        // WS3.20 bulk memory (trust-ir 4f09dab8). NOT in the Fragment-4 heap
        // arm: `HeapWalk` models a single-cell Store/Load, not a dynamic-count
        // byte copy or fill, so these refuse wherever they appear.
        Inst::MemCopy { .. } | Inst::MemSet { .. } => {
            "bulk MemCopy/MemSet (Fragment-4 models single-cell heap ops only)"
        }
        // trust-ir v47 `Drop`: a destructor run. Fragment-4's `HeapWalk` has
        // no destructor model, and reading it as a no-op would denote a
        // different program, so it refuses wherever it appears.
        Inst::Drop { .. } => {
            "Drop (a destructor run, trust-ir v47: no fragment models destructors)"
        }
        // trust-ir v50 `ArraySplat`: `n` copies of one register, built in
        // constant size. No fragment has an array vocabulary (their registers
        // are machine scalars or boxed `Nat`s), so it refuses wherever it
        // appears, and the refusal reads only the variant: never the length.
        Inst::ArraySplat { .. } => {
            "ArraySplat (a uniform register array, trust-ir v50: no fragment models arrays)"
        }
        // Runtime captures need a closure denotation and environment model.
        // No current fragment has either, even for an unused constructor.
        Inst::MakeClosure { .. } => {
            "MakeClosure (runtime captures, trust-ir v63: no fragment models closures)"
        }
        // A source-owned Box validity fact is not an ordinary heap-load or
        // pointer-copy license. No current denotation fragment models it.
        Inst::BoxDeref { .. } => {
            "BoxDeref (nominal source validity and pointee semantics are outside every fragment)"
        }
        // trust-ir v67-v69 tensor instructions compute whole tensor values
        // (contractions, element maps, reductions, views, gathers, scatters).
        // No fragment has a tensor vocabulary, so each refuses by name.
        Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. } => {
            "tensor instruction (trust-ir v67-v69: no fragment models tensor values)"
        }
        // Everything else, NAMED rather than wildcarded. Each dispatch's refusal
        // arm names its own variants too (`insts!`), so a variant trust-ir adds
        // fails to compile at every dispatch AND here, where it gets a label.
        Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::FCmp { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::IsUnique { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::AssertInvoke { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::DropInvoke { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. }
        | Inst::DialectOp(..)
        | Inst::MakeAggregate { .. } => "construct outside the fragment (fail-closed)",
    };
    format!(
        "{label} — the fragment is single-block Const/BinOp{{Add,Sub,Mul}}/heap-op/Return \
         (Fragment-2/4) or an entry ICmp+CondBr diamond over two return arms (Fragment-3a)"
    )
}

// --- Source side: kernel definition Expr -> denotation -----------------------

/// Fragment-4 source-side record vocabulary: which application heads are
/// single-constructor aggregate INTRODUCTION (`S.mk`) and field PROJECTION
/// (`S.<field>`), derived from the emitted module's `StructDef` table at mint
/// time (the module is the source of truth for which record types exist).
///
/// The source rules are pure substitution — the source side never sees the
/// heap: `[[S.<field_j> (S.mk a_0 … a_{n-1})]] = [[a_j]]`. A ctor application
/// anywhere OTHER than directly under a matching projection is out of
/// fragment (fail-closed). Projection heads are recognized LAST, so they can
/// never shadow the arithmetic/comparison/callee vocabulary.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RecordVocab {
    /// Projection head name -> (ctor head name, field index, field count).
    projections: BTreeMap<String, (String, usize, usize)>,
}

impl RecordVocab {
    /// The empty vocabulary (record-free fragments).
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Derive the vocabulary from the module's struct table: a struct `S`
    /// with fields `f…` gets ctor head `S.mk` and projection heads
    /// `S.<field>` (the Clean/Lean structure naming convention).
    #[must_use]
    pub fn from_module(module: &Module) -> Self {
        let mut projections = BTreeMap::new();
        for sd in &module.structs {
            let ctor = format!("{}.mk", sd.name);
            for (j, field) in sd.fields.iter().enumerate() {
                projections.insert(
                    format!("{}.{}", sd.name, field.name),
                    (ctor.clone(), j, sd.fields.len()),
                );
            }
        }
        RecordVocab { projections }
    }
}

/// Denote the decl's ORIGINAL kernel definition into the shared vocabulary.
///
/// Expects `fun (x1 ... xn : UIntW) => body` (possibly `n = 0`, i.e. a bare
/// body) and denotes `body`. Bound variables keep their de Bruijn indices
/// (see [`TvDenotation::body`]); the binder telescope must be homogeneous at
/// the `UIntW` matching `width`. A `let` binder of type `UIntW` inside `body`
/// is zeta-substituted (WS6.6), so the result never contains a `let`.
/// Fail-closed outside the fragment. Inline class dictionaries are projected
/// from their actual fields; named dictionaries require
/// [`denote_source_in_environment`] and otherwise refuse.
///
/// `callees` is the canonical callee list from the EMITTED side
/// ([`TvDenotation::callees`]): a source application `g a…` whose head names a
/// listed callee denotes to that callee's pinned symbol (Fragment-3b). Pass
/// `&[]` for the call-free fragments — then any application head that is not a
/// recognized arithmetic/comparison form is out of fragment.
///
/// `records` is the Fragment-4 source record vocabulary
/// ([`RecordVocab::from_module`]); pass [`RecordVocab::empty`] for the
/// record-free fragments.
///
/// # Errors
///
/// [`ReflectError::Unsupported`] for any construct outside the source
/// fragment (see the module docs' label table).
pub fn denote_source(
    defn: &Expr,
    width: u32,
    callees: &[(String, usize)],
    records: &RecordVocab,
) -> Result<TvDenotation, ReflectError> {
    denote_source_with_requirements(defn, width, callees, records, None)
        .and_then(SourceDenotation::into_legacy_model)
}

/// As [`denote_source`], resolving named class dictionaries in the ORIGINAL
/// source environment. The stored field determines the operation or literal;
/// its class/index/name is never assumed to determine its value.
pub fn denote_source_in_environment(
    defn: &Expr,
    width: u32,
    callees: &[(String, usize)],
    records: &RecordVocab,
    environment: &clean_kernel::Environment,
) -> Result<TvDenotation, ReflectError> {
    denote_source_with_requirements(defn, width, callees, records, Some(environment))
        .and_then(SourceDenotation::into_legacy_model)
}

/// A proposed source model and the additional original-source judgment its
/// construction requires. A Nat transcription alone cannot justify replacing
/// a propositional `ite` and its actual Decidable instance with a Bool choice.
#[derive(Debug, Clone)]
pub struct SourceDenotation {
    /// Proposed Nat model, whose provenance is still an external obligation.
    pub denotation: TvDenotation,
    /// The walk used a propositional ite, including one exposed by a field.
    pub requires_original_source_equation: bool,
}

impl SourceDenotation {
    fn into_legacy_model(self) -> Result<TvDenotation, ReflectError> {
        if self.requires_original_source_equation {
            return Err(ReflectError::unsupported(
                "propositional ite requires denote_source_with_requirements and a checked original-source equation; the legacy API cannot erase that obligation",
            ));
        }
        Ok(self.denotation)
    }
}

/// Denote source while recording proof requirements encountered during the
/// actual walk, including inside projected dictionary fields. A certificate
/// producer must discharge these requirements before minting evidence.
///
/// # Errors
/// Refuses the same unsupported shapes as [`denote_source_in_environment`].
pub fn denote_source_with_requirements(
    defn: &Expr,
    width: u32,
    callees: &[(String, usize)],
    records: &RecordVocab,
    environment: Option<&clean_kernel::Environment>,
) -> Result<SourceDenotation, ReflectError> {
    let uint_name = format!("UInt{width}");

    // Strip the lambda telescope, requiring every binder type to be `UIntW`.
    let mut arity = 0usize;
    let mut body = defn;
    while let ExprKind::Lam(_, ty, inner) = body.kind() {
        if !is_const_named(ty, &uint_name) {
            return Err(ReflectError::unsupported(format!(
                "binder type {ty} (source fragment binds {uint_name} params only, \
                 fail-closed)"
            )));
        }
        arity += 1;
        body = inner;
    }

    // Callee name -> (pinned symbol bvar, arity). Callees are OUTER binders, so
    // the symbol index sits above the `arity` param binders.
    let callee_syms: BTreeMap<String, (u32, usize)> = callees
        .iter()
        .enumerate()
        .map(|(j, (name, ca))| {
            (
                name.clone(),
                (callee_symbol_bvar(arity, callees.len(), j), *ca),
            )
        })
        .collect();

    let m = modulus(width);
    #[allow(clippy::cast_possible_truncation)]
    let cx = SrcCtx {
        width,
        uint_name: &uint_name,
        arity: arity as u32,
        m: &m,
        callee_syms: &callee_syms,
        records,
        instances: SourceInstances::new(environment),
        requires_original_source_equation: std::cell::Cell::new(false),
    };
    let den_body = denote_source_body(body, &cx, &[])?;
    Ok(SourceDenotation {
        denotation: TvDenotation {
            arity,
            width,
            body: den_body,
            callees: callees.to_vec(),
        },
        requires_original_source_equation: cx.requires_original_source_equation.get(),
    })
}

/// Denote the ORIGINAL kernel definition of a decl whose EMITTED function
/// returns a BOXED `Nat` (Fragment-5), into a `Nat` denotation.
///
/// This session's sound floor is a PARAMETER-FREE `Nat` constant (`Nat`, e.g.
/// `UIntN.size = Nat(Small(256))` / `2^64`), whose source body is a bare `Nat`
/// literal or a closed `Nat.{add,mul,sub,div,mod}` / `OfNat.ofNat Nat`
/// expression — the exact bignum ops the emitted `l_Nat_*` rows compute, so the
/// two denotations are kernel-def-eq. Fail-closed on `Nat` binders (parameter
/// rows are the ladder) and any non-`Nat` construct.
///
/// # Errors
///
/// [`ReflectError::Unsupported`] for any construct outside this floor.
pub fn denote_source_nat(
    defn: &Expr,
    callees: &[(String, usize)],
) -> Result<TvDenotation, ReflectError> {
    denote_source_nat_with_instances(defn, callees, None)
}

/// [`denote_source_nat`] with dictionary definitions from the source environment.
pub fn denote_source_nat_in_environment(
    defn: &Expr,
    callees: &[(String, usize)],
    environment: &clean_kernel::Environment,
) -> Result<TvDenotation, ReflectError> {
    denote_source_nat_with_instances(defn, callees, Some(environment))
}

fn denote_source_nat_with_instances(
    defn: &Expr,
    callees: &[(String, usize)],
    environment: Option<&clean_kernel::Environment>,
) -> Result<TvDenotation, ReflectError> {
    // Parameter-carrying Nat sources are the documented ladder: reject a
    // lambda telescope fail-closed rather than misdenote a bound var.
    if let ExprKind::Lam(..) = defn.kind() {
        return Err(ReflectError::unsupported(
            "Fragment-5 source with parameters (this floor covers parameter-free Nat \
             constants only, fail-closed)"
                .to_string(),
        ));
    }
    let callee_syms: BTreeMap<String, (u32, usize)> = callees
        .iter()
        .enumerate()
        .map(|(j, (name, ca))| (name.clone(), (callee_symbol_bvar(0, callees.len(), j), *ca)))
        .collect();
    let instances = SourceInstances::new(environment);
    let body = denote_source_nat_body(defn, &callee_syms, &instances)?;
    Ok(TvDenotation {
        arity: 0,
        width: 64,
        body,
        callees: callees.to_vec(),
    })
}

/// Denote a parameter-free source `Nat` expression (Fragment-5 floor): a bare
/// `Nat` literal, a pinned-callee application, or a closed
/// `Nat.{add,mul,sub,div,mod}` / `OfNat.ofNat Nat` tree. Fail-closed otherwise.
fn denote_source_nat_body(
    e: &Expr,
    callee_syms: &BTreeMap<String, (u32, usize)>,
    instances: &SourceInstances<'_>,
) -> Result<Expr, ReflectError> {
    // Bare Nat literal (any magnitude — Nat is unbounded).
    if let ExprKind::Lit(Literal::Nat(n)) = e.kind() {
        if let Some(v) = n.to_u64() {
            return Ok(Expr::nat_lit(v));
        }
        // >= 2^64: reconstruct from two little-endian limbs if it fits u128.
        let limbs = n.limbs();
        if limbs.iter().skip(2).all(|&l| l == 0) {
            let lo = u128::from(limbs.first().copied().unwrap_or(0));
            let hi = u128::from(limbs.get(1).copied().unwrap_or(0));
            return Ok(Expr::nat_lit_u128(lo | (hi << 64)));
        }
        return Err(ReflectError::unsupported(
            "source Nat literal >= 2^128 (fail-closed)".to_string(),
        ));
    }

    let head = e.get_app_fn();
    let args = e.get_app_args();
    let args: &[&Expr] = args.as_slice();
    let ExprKind::Const(head_name, _) = head.kind() else {
        return Err(ReflectError::unsupported(format!(
            "source Nat construct {e} (head is not a recognized constant, fail-closed)"
        )));
    };
    let head_name = source_head_name(head_name)?;

    // Pinned-callee application (compositional, same symbol the emitted side uses).
    if let Some((sym, ca)) = callee_syms.get(&head_name) {
        if args.len() != *ca {
            return Err(ReflectError::unsupported(format!(
                "source call to `{head_name}` has {} arg(s), the emitted callee takes {ca} \
                 (fail-closed)",
                args.len()
            )));
        }
        let mut arg_dens = Vec::with_capacity(args.len());
        for a in args {
            arg_dens.push(denote_source_nat_body(a, callee_syms, instances)?);
        }
        return Ok(Expr::apps(Expr::bvar(*sym), arg_dens));
    }

    // `OfNat.ofNat Nat k inst` literal.
    if head_name == "OfNat.ofNat" && args.len() == 3 && is_const_named(args[0], "Nat") {
        let field = instances.field(args[2], "OfNat.mk", &args[..2])?;
        return denote_source_nat_body(&field, callee_syms, instances);
    }

    // Bignum arithmetic — the SAME kernel constants the emitted `l_Nat_*` rows
    // produce (no width wrap; monus / n/0=0 / n%0=n conventions match).
    let bin = |f: &str| -> Result<Expr, ReflectError> {
        if args.len() != 2 {
            return Err(ReflectError::unsupported(format!(
                "`{head_name}` with {} arg(s) (expected 2, fail-closed)",
                args.len()
            )));
        }
        let a = denote_source_nat_body(args[0], callee_syms, instances)?;
        let b = denote_source_nat_body(args[1], callee_syms, instances)?;
        Ok(nat_app2(f, a, b))
    };
    match head_name.as_str() {
        "Nat.add" => return bin("Nat.add"),
        "Nat.mul" => return bin("Nat.mul"),
        "Nat.sub" => return bin("Nat.sub"),
        "Nat.div" => return bin("Nat.div"),
        "Nat.mod" => return bin("Nat.mod"),
        _ => {}
    }

    Err(ReflectError::unsupported(format!(
        "source Nat construct headed by `{head_name}` (Fragment-5 floor is Nat \
         literals / pinned-callee applications / Nat.add|mul|sub|div|mod only, \
         fail-closed)"
    )))
}

/// Whether `e` is exactly the constant `name` (any universe levels).
fn is_const_named(e: &Expr, name: &str) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if *n == Name::from_string(name))
}

/// Names exposed by dictionary reduction were not necessarily present in the
/// original expression's identity walk. Never give a display twin a primitive
/// or callee's meaning, or admit the compiler's reserved typed-wire namespace.
fn source_head_name(name: &Name) -> Result<String, ReflectError> {
    let label = name.to_string();
    if Name::from_string(&label) != *name || label.starts_with("__clean_typed_v1_") {
        return Err(ReflectError::unsupported(
            "source identity is unmeasured for escaped typed names (fail-closed)".to_string(),
        ));
    }
    Ok(label)
}

/// Extract a `Nat` literal < 2^width from a kernel literal expr.
fn source_nat_literal(e: &Expr, width: u32) -> Option<u64> {
    if let ExprKind::Lit(Literal::Nat(n)) = e.kind() {
        let v = n.to_u64()?;
        if width == 64 || u128::from(v) < (1u128 << width) {
            return Some(v);
        }
    }
    None
}

/// The fixed context of one source-side denotation: the fragment width, the
/// `UIntW` name, the parameter count, the modulus, the pinned callee symbols
/// and the record vocabulary. Only the `let` environment varies during the
/// walk (see [`denote_source_body`]).
struct SrcCtx<'a> {
    width: u32,
    uint_name: &'a str,
    arity: u32,
    m: &'a Expr,
    callee_syms: &'a BTreeMap<String, (u32, usize)>,
    records: &'a RecordVocab,
    instances: SourceInstances<'a>,
    requires_original_source_equation: std::cell::Cell<bool>,
}

/// Denote a source-side `UIntW`-valued expression.
///
/// `lets` is the environment of enclosing source `let` binders, innermost
/// LAST, each entry the DENOTATION of the bound value (WS6.6). A source bvar
/// `i` under `k = lets.len()` lets therefore names `lets[k - 1 - i]` when
/// `i < k`, and otherwise parameter binder `i - k`, which keeps its
/// Fragment-2 index `bvar(i - k)` in the denotation telescope. Substituting
/// the bound value's denotation is exactly the kernel's zeta rule
/// (`let x := v; b ≡ b[v/x]`), so the comparand this produces is let-free and
/// uses only the vocabulary the emitted side already uses: the pinned
/// trust-ir re-checker, which rebuilds the statement from its re-derived LHS
/// and the carried comparand, needs nothing new. The denotations are shared
/// (`Expr` is reference counted), so a chain of `let`s is walked once each,
/// never re-denoted per use.
fn denote_source_body(e: &Expr, cx: &SrcCtx<'_>, lets: &[Expr]) -> Result<Expr, ReflectError> {
    // Bound variable: an enclosing `let` (WS6.6) or one of the stripped
    // parameter binders. The source fragment introduces no other binders.
    if let ExprKind::BVar(i) = e.kind() {
        let k = lets.len();
        let i_us = *i as usize;
        if i_us < k {
            return Ok(lets[k - 1 - i_us].clone());
        }
        #[allow(clippy::cast_possible_truncation)]
        let j = (i_us - k) as u32;
        if j < cx.arity {
            return Ok(Expr::bvar(j));
        }
        return Err(ReflectError::unsupported(format!(
            "bvar #{i} escaping the {}-parameter telescope under {k} source let(s) \
             (fail-closed)",
            cx.arity
        )));
    }

    // WS6.6: a source `let x : UIntW := v; b` (what `let t := a + 1; t * t`
    // elaborates to). The binder type must be exactly the fragment's `UIntW`
    // — the value is denoted as a U-w value, so any other type (a `Bool`, a
    // `Nat`, a record) stays out of fragment. The value is denoted EAGERLY,
    // even when the body never uses it, so an out-of-fragment value is a
    // fail-closed skip rather than silently dropped.
    if let ExprKind::Let(_, ty, val, body, _) = e.kind() {
        if !is_const_named(ty, cx.uint_name) {
            return Err(ReflectError::unsupported(format!(
                "source let binding at type {ty} (a source let must bind a {} value, \
                 fail-closed)",
                cx.uint_name
            )));
        }
        let dv = denote_source_body(val, cx, lets)?;
        let mut inner = lets.to_vec();
        inner.push(dv);
        return denote_source_body(body, cx, &inner);
    }

    let (width, uint_name) = (cx.width, cx.uint_name);
    let head = e.get_app_fn();
    let args = e.get_app_args();
    let args: &[&Expr] = args.as_slice();
    let ExprKind::Const(head_name, _) = head.kind() else {
        return Err(ReflectError::unsupported(format!(
            "source construct {e} (head is not a recognized constant, fail-closed)"
        )));
    };
    let head_name = source_head_name(head_name)?;

    // Fragment-3b call: an application whose head names a pinned callee. Denote
    // to `G_callee` applied to the argument denotations — the SAME symbol the
    // emitted side uses, so the caller equation is kernel-decided over it.
    if let Some((sym, ca)) = cx.callee_syms.get(&head_name) {
        if args.len() != *ca {
            return Err(ReflectError::unsupported(format!(
                "source call to `{head_name}` has {} arg(s), the emitted callee takes {ca} \
                 — arity mismatch, fail-closed",
                args.len()
            )));
        }
        let mut arg_dens = Vec::with_capacity(args.len());
        for a in args {
            arg_dens.push(denote_source_body(a, cx, lets)?);
        }
        return Ok(Expr::apps(Expr::bvar(*sym), arg_dens));
    }

    // Literals: `UIntW.ofNat k` or `OfNat.ofNat UIntW k inst`.
    if head_name == format!("{uint_name}.ofNat") && args.len() == 1 {
        if let Some(k) = source_nat_literal(args[0], width) {
            return Ok(Expr::nat_lit(k));
        }
        return Err(ReflectError::unsupported(format!(
            "{uint_name}.ofNat of a non-literal or out-of-range argument (fail-closed)"
        )));
    }
    if head_name == "OfNat.ofNat" && args.len() == 3 && is_const_named(args[0], uint_name) {
        let field = cx.instances.field(args[2], "OfNat.mk", &args[..2])?;
        return denote_source_body(&field, cx, lets);
    }

    // Arithmetic class dispatch is projection of an actual dictionary field.
    // Many valid HAdd dictionaries implement something other than addition.
    let class_constructor = match head_name.as_str() {
        "HAdd.hAdd" => Some(("HAdd.mk", 3)),
        "HSub.hSub" => Some(("HSub.mk", 3)),
        "HMul.hMul" => Some(("HMul.mk", 3)),
        "HAnd.hAnd" => Some(("HAnd.mk", 3)),
        "HOr.hOr" => Some(("HOr.mk", 3)),
        "HXor.hXor" => Some(("HXor.mk", 3)),
        "HShiftLeft.hShiftLeft" => Some(("HShiftLeft.mk", 3)),
        "HShiftRight.hShiftRight" => Some(("HShiftRight.mk", 3)),
        "ShiftLeft.shiftLeft" => Some(("ShiftLeft.mk", 1)),
        "ShiftRight.shiftRight" => Some(("ShiftRight.mk", 1)),
        "Add.add" => Some(("Add.mk", 1)),
        "Sub.sub" => Some(("Sub.mk", 1)),
        "Mul.mul" => Some(("Mul.mk", 1)),
        "AndOp.and" => Some(("AndOp.mk", 1)),
        "OrOp.or" => Some(("OrOp.mk", 1)),
        _ => None,
    };
    if let Some((constructor, params)) = class_constructor {
        if args.len() == params + 3
            && args[..params]
                .iter()
                .all(|ty| is_const_named(ty, uint_name))
        {
            if matches!(
                constructor,
                "HXor.mk" | "HShiftLeft.mk" | "HShiftRight.mk" | "ShiftLeft.mk" | "ShiftRight.mk"
            ) {
                cx.requires_original_source_equation.set(true);
            }
            let field = cx
                .instances
                .field(args[params], constructor, &args[..params])?;
            let applied = cx.instances.apply(field, &args[params + 1..])?;
            return denote_source_body(&applied, cx, lets);
        }
    }

    // UInt shifts first reduce the amount modulo width, exactly as the
    // original checked prelude does. This proposed Nat model always requires
    // a checked equation against that original source before minting.
    if args.len() == 2
        && (head_name == format!("{uint_name}.shiftLeft")
            || head_name == format!("{uint_name}.shiftRight"))
    {
        cx.requires_original_source_equation.set(true);
        let a = denote_source_body(args[0], cx, lets)?;
        let b = denote_source_body(args[1], cx, lets)?;
        let amount = nat_app2("Nat.mod", b, Expr::nat_lit(u64::from(cx.width)));
        let op = if head_name.ends_with(".shiftLeft") {
            BinOp::Shl
        } else {
            BinOp::LShr
        };
        return denote_binop(op, a, amount, cx.m);
    }

    // Bare UIntW primitives carry their ratified wrapping/bitwise semantics.
    let op = if head_name == format!("{uint_name}.add") && args.len() == 2 {
        Some((BinOp::Add, args[0], args[1]))
    } else if head_name == format!("{uint_name}.sub") && args.len() == 2 {
        Some((BinOp::Sub, args[0], args[1]))
    } else if head_name == format!("{uint_name}.mul") && args.len() == 2 {
        Some((BinOp::Mul, args[0], args[1]))
    } else if head_name == format!("{uint_name}.land") && args.len() == 2 {
        Some((BinOp::And, args[0], args[1]))
    } else if head_name == format!("{uint_name}.lor") && args.len() == 2 {
        Some((BinOp::Or, args[0], args[1]))
    } else if head_name == format!("{uint_name}.xor") && args.len() == 2 {
        Some((BinOp::Xor, args[0], args[1]))
    } else {
        None
    };
    if let Some((op, a, b)) = op {
        if op == BinOp::Xor {
            // The UInt wrap must be justified against the original checked
            // definition, including dictionary fields. A Nat model alone
            // cannot mint this source binding.
            cx.requires_original_source_equation.set(true);
        }
        let da = denote_source_body(a, cx, lets)?;
        let db = denote_source_body(b, cx, lets)?;
        return denote_binop(op, da, db, cx.m);
    }

    // Ordinary Lean `if` uses a proposition and its actual Decidable value.
    // This is only a proposed Nat model. Record the requirement at the point
    // of use, including an ite exposed by dictionary projection, so the
    // minter must prove the full original-source equation independently.
    if head_name == "ite" && args.len() == 5 && is_const_named(args[0], uint_name) {
        let c = denote_source_prop_cond(args[1], cx, lets)?;
        let t = denote_source_body(args[3], cx, lets)?;
        let e = denote_source_body(args[4], cx, lets)?;
        cx.requires_original_source_equation.set(true);
        return Ok(ite_nat(c, t, e));
    }

    // Fragment-3a conditional (the source `if cmp then t else e` on a Bool
    // comparison). Recognized in the three shapes a Clean/Lean `Bool`-eliminator
    // takes — the applicative `cond α c t e`, the recursor `Bool.rec motive e t
    // c`, and the case-analysis `Bool.casesOn motive c e t` — all denoted to the
    // same shared `ite_nat`. The condition is denoted by [`denote_source_cond`]
    // (a Bool-valued comparison); the arms recurse as UIntW values.
    if head_name == "cond" && args.len() == 4 {
        let c = denote_source_cond(args[1], cx, lets)?;
        let t = denote_source_body(args[2], cx, lets)?;
        let e = denote_source_body(args[3], cx, lets)?;
        return Ok(ite_nat(c, t, e));
    }
    if head_name == "Bool.rec" && args.len() == 4 {
        // @Bool.rec motive (falseMinor) (trueMinor) (major)
        let e = denote_source_body(args[1], cx, lets)?;
        let t = denote_source_body(args[2], cx, lets)?;
        let c = denote_source_cond(args[3], cx, lets)?;
        return Ok(ite_nat(c, t, e));
    }
    if head_name == "Bool.casesOn" && args.len() == 4 {
        // @Bool.casesOn motive (major) (falseMinor) (trueMinor)
        let c = denote_source_cond(args[1], cx, lets)?;
        let e = denote_source_body(args[2], cx, lets)?;
        let t = denote_source_body(args[3], cx, lets)?;
        return Ok(ite_nat(c, t, e));
    }

    // Fragment-4 field projection of a single-constructor aggregate: pure
    // substitution `[[S.f_j (S.mk a_0 … a_{n-1})]] = [[a_j]]`. Recognized
    // LAST so record names can never shadow the vocabulary above; a ctor
    // application anywhere else falls through to the fail-closed error.
    if let Some((ctor, idx, n)) = cx.records.projections.get(&head_name) {
        let [obj] = args else {
            return Err(ReflectError::unsupported(format!(
                "projection `{head_name}` applied to {} argument(s) (expected exactly the \
                 record value, fail-closed)",
                args.len()
            )));
        };
        let obj_head = obj.get_app_fn();
        let obj_args = obj.get_app_args();
        if !is_const_named(obj_head, ctor) || obj_args.len() != *n {
            return Err(ReflectError::unsupported(format!(
                "projection `{head_name}` of a non-constructor value (Fragment-4 source \
                 projections apply to `{ctor}` applications of {n} field(s) only, \
                 fail-closed)"
            )));
        }
        return denote_source_body(obj_args[*idx], cx, lets);
    }

    Err(ReflectError::unsupported(format!(
        "source construct headed by `{head_name}` (source fragment is \
         {uint_name} vars/literals/add/sub/mul, {uint_name} lets, a Bool-comparison \
         conditional, pinned callee applications, and record field projections of a \
         matching constructor application only, fail-closed)"
    )))
}

/// Read the actual order dictionary field before proposing a Bool model for
/// a UInt proposition. Neither the LT/LE method name nor the instance name
/// determines which relation the checked dictionary implements.
fn denote_source_prop_cond(e: &Expr, cx: &SrcCtx<'_>, lets: &[Expr]) -> Result<Expr, ReflectError> {
    let head = e.get_app_fn();
    let args = e.get_app_args();
    let ExprKind::Const(name, _) = head.kind() else {
        return Err(ReflectError::unsupported(
            "source proposition has no recognized order head",
        ));
    };
    let name = source_head_name(name)?;
    let constructor = match name.as_str() {
        "LT.lt" => Some("LT.mk"),
        "LE.le" => Some("LE.mk"),
        _ => None,
    };
    if let Some(constructor) = constructor {
        if args.len() == 4 && is_const_named(args[0], cx.uint_name) {
            let field = cx.instances.field(args[1], constructor, &args[..1])?;
            let applied = cx.instances.apply(field, &args[2..])?;
            return denote_source_prop_cond(&applied, cx, lets);
        }
    }
    let comparison = if name == format!("{}.lt", cx.uint_name) {
        Some("Nat.blt")
    } else if name == format!("{}.le", cx.uint_name) {
        Some("Nat.ble")
    } else {
        None
    };
    if let Some(comparison) = comparison {
        if args.len() == 2 {
            return Ok(nat_app2(
                comparison,
                denote_source_body(args[0], cx, lets)?,
                denote_source_body(args[1], cx, lets)?,
            ));
        }
    }
    Err(ReflectError::unsupported(format!(
        "source proposition headed by `{name}` is outside the UInt order fragment (fail-closed)"
    )))
}

/// Denote a source-side BOOLEAN condition into the shared vocabulary: a
/// `UIntW.{blt,ble,beq}` comparison over two UIntW-valued subexpressions,
/// mapping to `Nat.{blt,ble,beq}` (the transcription of trust-ir's unsigned
/// `ICmp` — faithful on the U-w domain). Fail-closed on anything else.
fn denote_source_cond(e: &Expr, cx: &SrcCtx<'_>, lets: &[Expr]) -> Result<Expr, ReflectError> {
    let uint_name = cx.uint_name;
    let head = e.get_app_fn();
    let args = e.get_app_args();
    let args: &[&Expr] = args.as_slice();
    let ExprKind::Const(head_name, _) = head.kind() else {
        return Err(ReflectError::unsupported(format!(
            "source condition {e} (head is not a recognized comparison constant, fail-closed)"
        )));
    };
    let head_name = source_head_name(head_name)?;
    let cmp = if head_name == format!("{uint_name}.blt") && args.len() == 2 {
        Some(("Nat.blt", args[0], args[1]))
    } else if head_name == format!("{uint_name}.ble") && args.len() == 2 {
        Some(("Nat.ble", args[0], args[1]))
    } else if head_name == format!("{uint_name}.beq") && args.len() == 2 {
        Some(("Nat.beq", args[0], args[1]))
    } else {
        None
    };
    if let Some((f, a, b)) = cmp {
        let da = denote_source_body(a, cx, lets)?;
        let db = denote_source_body(b, cx, lets)?;
        return Ok(nat_app2(f, da, db));
    }
    Err(ReflectError::unsupported(format!(
        "source condition headed by `{head_name}` (Fragment-3a conditions are \
         {uint_name}.blt / {uint_name}.ble / {uint_name}.beq only, fail-closed)"
    )))
}

// --- The equation the kernel decides -----------------------------------------

/// The fully-qualified per-decl theorem name the certificate cites:
/// `CleanTV.<function-name>.denotes`. The trust-ir re-checker RE-DERIVES this
/// from the module function and rejects any other citation.
#[must_use]
pub fn tv_theorem_name(func_name: &str) -> String {
    format!("CleanTV.{func_name}.denotes")
}

/// Schema identifier for the [`tv_statement_formula`] payload — the SINGLE
/// spelling both the minter (`clean-compiler`'s `emit_trust_ir_tv`) and any
/// cross-module importer read. A consumer that does not recognize this schema
/// must refuse the clause, never guess at its payload.
pub const CLEAN_TV_FORMULA_SCHEMA: &str = "clean-backend-tv.denotes@1";

/// The backend-TV obligation's carried STATEMENT, as a
/// [`trust_ir::proof::ProofFormula`].
///
/// # Why this has to exist
///
/// A `TranslationValidation` obligation minted with `formula: None` cannot be
/// inherited across a crate boundary at all. `trust_ir_build`'s linked
/// validator refuses both directions explicitly — "far obligation #N carries
/// no formula; a claim with no statement cannot be restated" and "local
/// restatement obligation #N carries no formula; an inherited claim must be
/// stated, not implied" — so until the TV obligation states its own claim, a
/// Clean library's certified decl is unimportable by construction, however
/// well kernel-checked it is. That refusal is right: an importer cannot restate
/// what the dependency never wrote down.
///
/// # Why the payload is a function of `(symbol, arity, width)` and nothing else
///
/// An importer must be able to RE-DERIVE this text from the far
/// `Function::name` and the far `FuncTy` alone, and then require the far
/// obligation's recorded formula to be byte-equal to what it derived. If the
/// payload depended on anything the importer cannot read off the dependency's
/// own signature — the callee set, the proof term, the source file — the
/// importer would be reduced to COPYING A's formula, and the equality
/// `check_inherited` demands would be vacuous. So the payload is deliberately
/// exactly what a signature determines, and the claim it states is the
/// top-level equation, which [`tv_statement`] establishes PARAMETRICALLY in any
/// pinned callee symbols (hence unconditionally, at every interpretation) — the
/// callee set is how the equation is proved, not part of what it says.
///
/// # What the fields mean, including the absences
///
/// * `schema` — [`CLEAN_TV_FORMULA_SCHEMA`].
/// * `payload` — the statement text, in the one spelling above.
/// * `bindings` — one entry per parameter, binding `x{i}` to
///   `BitVec(width)` at `Param { index: i }`. The fragment is uniform-width by
///   construction, so every parameter has the same sort. Indices are `0..arity`
///   with `arity` read off the function's own parameter list, so they are in
///   range by construction; a test pins that, because the validator resolves
///   bindings on summary clauses only and would carry a wrong index silently.
/// * `smtlib` / `sort` — `None`, and NOT as a stand-in for agreement: this
///   claim is decided by the Clean kernel as a definitional-equality judgment,
///   not by an SMT solver, so there is no SMT-LIB2 rendering and no SMT sort to
///   record. Writing one would invent a second source of truth.
///
/// Note on lineage: `clean_cic_lineage_digest` hashes `schema`, `payload`,
/// `smtlib` and `sort` (but not `bindings`), so minting this MOVES the lineage
/// digest of every certified Clean decl. Measured before landing: nothing in
/// `~/clean`, `~/trust-cg` or `~/trust` stores such a digest — every consumer
/// recomputes it at use time — and the one site that compares it
/// (`emit_trust_ir_tv_tests.rs`) re-derives it from the same obligation, so it
/// moves in lockstep. The digest must therefore be taken AFTER the formula is
/// attached, which is why the minter builds the obligation complete and only
/// then calls `clean_cic_lineage_digest`.
#[must_use]
pub fn tv_statement_formula(symbol: &str, arity: u32, width: u32) -> trust_ir::proof::ProofFormula {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort, ProofFormula};

    let theorem = tv_theorem_name(symbol);
    let args: Vec<String> = (0..arity).map(|i| format!("x{i}")).collect();
    let binder = if args.is_empty() {
        String::new()
    } else {
        format!("forall ({} : u{width}), ", args.join(" "))
    };
    let applied = if args.is_empty() {
        String::new()
    } else {
        format!(" {}", args.join(" "))
    };
    let payload = format!(
        "{theorem}: {binder}denote(emitted {symbol}){applied} = \
         denote(source {symbol}){applied} (mod 2^{width})"
    );
    let bindings = (0..arity)
        .map(|i| {
            (
                format!("x{i}"),
                ClauseBinding {
                    sort: ClauseSort::BitVec(width),
                    place: ClausePlace::Param { index: i },
                },
            )
        })
        .collect();
    ProofFormula {
        schema: CLEAN_TV_FORMULA_SCHEMA.to_string(),
        payload,
        // Deliberately absent: the judgment is kernel definitional equality,
        // not an SMT query. See the doc comment above.
        smtlib: None,
        sort: None,
        bindings,
    }
}

/// The TV theorem STATEMENT:
/// `∀ (G0 … : Nat^…→Nat) (x1 … xn : Nat), @Eq.{1} Nat lhs rhs`.
///
/// A `Prop`, as `Declaration::Theorem` requires. `callee_arities` gives the
/// arity of each pinned callee symbol (Fragment-3b), bound as OUTER
/// `Nat^arity → Nat` variables above the `param_arity` `Nat` params; pass `&[]`
/// for the call-free fragments. The kernel decides it via [`tv_proof_term`]:
/// `check_type` reduces to definitional equality of `lhs` and `rhs` under the
/// binders — the actual translation-validation judgment (parametric in the
/// callee symbols, so it holds at every interpretation, hence at the callees'
/// certified meaning).
pub fn tv_statement(callee_arities: &[usize], param_arity: usize, lhs: &Expr, rhs: &Expr) -> Expr {
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), lhs.clone(), rhs.clone()],
    );
    // Inner: the `param_arity` Nat params.
    let with_params = (0..param_arity).fold(eq, |acc, _| Expr::pi(BinderInfo::Default, nat(), acc));
    // Outer: the callee symbols (iterating in reverse so the bvar indices match
    // `callee_symbol_bvar`).
    callee_arities.iter().rev().fold(with_params, |acc, ca| {
        Expr::pi(BinderInfo::Default, callee_fn_ty(*ca), acc)
    })
}

/// The TV proof term: `fun (G0 …) (x1 … xn : Nat) => @Eq.refl.{1} Nat lhs`.
///
/// Checks against [`tv_statement`] exactly when the kernel finds `lhs` and
/// `rhs` definitionally equal as open terms — the kernel is not told the
/// answer, it decides it.
pub fn tv_proof_term(callee_arities: &[usize], param_arity: usize, lhs: &Expr) -> Expr {
    let refl = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), lhs.clone()],
    );
    let with_params =
        (0..param_arity).fold(refl, |acc, _| Expr::lam(BinderInfo::Default, nat(), acc));
    callee_arities.iter().rev().fold(with_params, |acc, ca| {
        Expr::lam(BinderInfo::Default, callee_fn_ty(*ca), acc)
    })
}

#[cfg(test)]
#[path = "denote_tests.rs"]
mod tests;

// WS5.12: the `let` rule against the kernel — elaborator-shaped positives,
// agreement with the kernel's own zeta, the non-wrapping-op negative twin,
// the wrong-de-Bruijn-shift mutation control, and the Nat-floor scope pin.
#[cfg(test)]
#[path = "denote_ws5_12_tests.rs"]
mod ws5_12_tests;

#[cfg(test)]
#[path = "denote_runtime_closure_tests.rs"]
mod runtime_closure_tests;

#[cfg(test)]
#[path = "tensor_fragment_refusal_tests.rs"]
mod tensor_fragment_refusal_tests;

#[cfg(test)]
#[path = "nominal_fragment_refusal_tests.rs"]
mod nominal_fragment_refusal_tests;

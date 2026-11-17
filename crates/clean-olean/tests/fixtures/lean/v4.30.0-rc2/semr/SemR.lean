/-
  SemR — one semantics of trust-ir level R (Trust's proven-core plan, RM4), v1.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>

  This file is SemR's syntax and semantics: level R's syntax as Lean
  inductives, its binary decoder (the wire bytes
  `trust_ir::binary::serialize_module` writes, read straight off the byte
  list), its scalar operator layer, its small-step relation `Step` (one rule
  per instruction) and the run relation `Exec` over it, the executable
  `stepCore`/`run`, and the theorems that tie them: `step_sound` and
  `step_complete` (the executable step IS the relation), `run_sound`,
  `run_complete`, `exec_det`. It imports nothing beyond Lean's `Init`.
  `SemRMiniRust.lean` proves the operator layer is MiniRust's generated
  operators (`MiniRust.lean`), for every integer type; `SemRMemory.lean`
  proves the memory layer's laws (a load reads back what a store wrote, a
  disjoint store leaves it alone, a dead slot or an access past its end is
  undefined behaviour), that an integer's bytes are MiniRust's little-endian
  encoding both ways, that the alignment, liveness and bounds checks are
  MiniRust's, and that an allocation's address is one MiniRust may pick.

  Rules of the file (RM4's deliverable text):
  * no `native_decide`, no `partial def`, no `sorry`, no `axiom`, no
    `implemented_by`/`extern`: every definition is total by structural
    recursion and every theorem kernel-checks with a closure in Ax0
    (`propext`, `Classical.choice`, `Quot.sound`);
  * no `Int` division or remainder anywhere: Lean's `Int` `/` and `%` round
    differently from Clean's prelude ones (Clean's `clean check` decides
    `(-7 : Int) / 2 = -3`, Lean `-4`), so every integer is its `w`-bit
    RESIDUE as a `Nat` in `[0, 2^w)` and the signed operations are spelled on
    magnitudes;
  * fail closed: a construct outside the fragment is `unsupported <feature>`
    (by name), never a default.

  The fragment v0 decodes and runs is the scalar/control-flow core of the
  trust-ir conformance corpus: integer and `Bool` arithmetic (`BinOp`,
  `UnOp`, the checked `Overflow` trio), `ICmp`, `Select`, `Copy`, `Const`
  (integers, `Bool`, the null pointer, enum variants, content-addressed
  tensors), enum and flat scalar struct
  lane projections (`ExtractField` / `InsertField`), binding frames (`OpenFrame`, `BindSlot`,
  `LoadSlot`, `CloseFrame`), `NullPtr`, and `Br` / `CondBr` / `Return`, in a
  module with either the canonical targetless 64-bit layout or an explicit
  canonical little-endian 32/64-bit target record.
  The decoder reads the producer's proof annotations and textual proof
  obligations without granting them authority, fieldless enums with
  explicit discriminants, integer casts and `switch` (VF5's D-2(b)).
  The typed private-cell extension is an abstract allocation model, not
  byte-addressed Rust memory; its operations are NOT admitted by the binary
  decoder. Source, layout, provenance and concurrency claims require separate
  refinements.

  Quoted models additionally construct and project nominal closure values
  with exact captures and a checked capture-prefix target signature. These
  value operations neither invoke the target nor allocate memory. Closure tables, v63 construction
  bytes and closure application remain outside the binary decoder and fragment.

  The tensor region (v67) adds integer tensors (`Ty.tensor`: an integer element
  type and a rank; the extents are runtime values the tensor carries) and
  their contraction (`TensorContract`, XLA's DotGeneral: batch and contracted
  axis pairs, each result element the wrapping sum, a left fold in row-major
  order, of the wrapping products). Shape agreement is a precondition:
  paired extents that differ, and a result too large for `usize`, are
  undefined behaviour. A float element is refused by name
  (`tensor.float_element`): SemR has no float model. Tensors have no memory
  layout; they enter as entry arguments and leave as returned values.
  `TensorContraction.lean` proves an integer matrix multiply by this
  instruction equals its loop nest, for every shape.

  Wire v68 adds the tensor map, reduction and view. `TensorMap` runs a
  scalar body (`MapNode`s: `BinOp`, `UnOp`, `ICmp`, `Select` and the integer
  `Cast`s over lane numbers) at every coordinate of its tensor operands, in
  row-major order, through the scalar instructions' own evaluators, whose
  verdicts (a division by zero, …) are the node's; operands whose extents
  differ are undefined behaviour. `TensorReduce` folds a source along
  strictly ascending axes by `add`, `mul`, `and`, `or`, `xor` or a signed or
  unsigned minimum or maximum, a left fold from the operator's identity in
  row-major order (`RowMajor`, the one order); a result too large for
  `usize` is undefined behaviour. `TensorView` maps each result coordinate to
  a source coordinate by a node list over the integers (`IxExpr`: literals,
  `usize` parameters, source extents, result coordinates, `+ - *`, Euclidean
  `div`/`rem`, `min`/`max`; Euclidean division spelled on magnitudes, per the
  rule above), its extents computed once from the coordinate-free nodes: a
  node value outside `[-2^127, 2^127)`, a divisor of zero, an extent outside
  `usize`, a result too large for `usize`, and an out-of-range source
  coordinate with no fill operand are undefined behaviour; with a fill, that
  element is the fill. Each instruction's static rules and its tensor
  operands' well-formedness are type errors, checked first, in the reference
  interpreter's order (`crates/trust-ir/src/interpret/tensor_region.rs`).

  Wire v69 adds the tensor gather and scatter, which index a tensor in
  coordinate form: one integer coordinate tensor per axis of the tensor they
  index, each of its own integer element type, its element read as the
  integer that type denotes (a signed residue at or above the sign bit is
  negative, outside every axis). `TensorGather` reads its data at the
  coordinates, the result having the coordinate tensors' extents.
  `TensorScatter` writes its source over a copy of its initial tensor at the
  coordinates, in the source's row-major order, so where several source
  positions name one coordinate the row-major-last write is the one the
  result holds. Coordinate tensors whose extents differ (from each other for
  the gather, from the source's for the scatter) and a coordinate outside
  its axis anywhere are undefined behaviour, decided before any element is
  read or written. The static rules (G1-G3, S1-S3) and each tensor operand's
  well-formedness are type errors, checked after the poison operands and
  before the preconditions (`docs/SPEC_RATIFICATIONS.md` §26).

  Wire v70 adds content-addressed weight blobs (§27). `Const.tensorBlob`
  names an integer tensor by the SHA-256 of its element bytes and by its
  extents; the module's blob table (`Module.blobs`) holds each digest once
  with its bytes, in strictly ascending digest order (any other order is
  malformed, as the binary reader refuses it). The constant reads its row
  when its `Const` runs (`blobVal`): a rank other than its type's, an extent
  outside `usize`, a digest no row holds, bytes that do not hash to the
  digest (`sha256`, FIPS 180-4, by structural recursion over `Nat`), and a
  byte count other than the extents' product times the element's width (or
  a product outside `usize`) are type errors, in the reference interpreter's
  order. The elements are the bytes read little-endian at that width, in
  row-major order. A body names the digest, never the bytes. A blob stands
  only as the whole value of a `Const` (rule C1): one nested in a struct
  field or an enum payload is a type error (`containsBlob`), as the
  interpreter refuses it.

  The first memory slice (RM4c) adds stack slots: `Alloca` (a slot of a
  scalar type, or a counted array of them, optionally over-aligned: the
  producer's `StorageLive`), `Load` and `Store` of integers and `Bool`s
  (plain or volatile, optionally at an explicit alignment) through a
  pointer, `GEP` (address arithmetic over a scalar element) and `Dealloc`
  (`StorageDead`). Memory has MiniRust's shape (`mem/basic.md`): a list of
  allocations, each live or dead, of abstract bytes (uninitialized, or a
  byte) at an address; a pointer is its allocation and its offset (its
  provenance); an integer is stored as its little-endian bytes
  (`SemRMemory.lean`: `encode_minirust`, `decode_minirust`). Using a dead
  slot, an access outside a slot, a misaligned address, a null pointer, and
  reading uninitialized bytes volatile (or inspecting them, read plainly) are
  undefined behaviour, each by the reference interpreter's reason; the
  liveness, alignment and bounds verdicts are MiniRust's `check_ptr` and
  `Align::is_aligned` on the same pointer (`accessAlloc_minirust`). A pointer
  is never stored in memory in this slice (a pointer-typed access is
  `unsupported`).

  SemR's verdicts are the reference interpreter's. Where MiniRust's differ,
  SemR follows the interpreter, except for a `Bool` byte (refused by name);
  trust-ir's `semr_memory_minirust_divergences_are_pinned` runs each of these
  through both engines:
  * allocation is the interpreter's bump allocator (addresses from 1024, each
    slot at the next free address rounded up to its alignment). That address
    is one MiniRust's `allocate` may pick (`alloc_fresh`: aligned, past every
    earlier allocation), but MiniRust picks among all of them, and a program
    is undefined behaviour if any pick makes it so. SemR runs the one choice,
    so a program whose alignment depends on where a slot lands (a `u16`
    access to a 2-byte `u8` slot: aligned at 1024, misaligned at 1025) is
    `Ok` or UB in SemR by the slots before it, and UB in MiniRust either way;
  * a plain integer `Load` of uninitialized bytes is poison that keeps its
    bytes (the interpreter's `PartialBytes`), undefined behaviour only once
    inspected or stored volatile; MiniRust's typed load of an integer from
    uninitialized bytes is undefined behaviour at the load;
  * `GEP`'s `inbounds` flag is decoded and ignored, as by the interpreter: an
    `inbounds` offset past its slot, or from a dead slot, is a pointer;
    MiniRust's in-bounds offset is undefined behaviour there;
  * `Return` frees nothing (level R deallocates a slot only by an explicit
    `Dealloc`); MiniRust frees a frame's locals at its return, so a caller's
    access to a callee's slot is undefined behaviour there;
  * on a dead, misaligned pointer SemR names the interpreter's reason (use
    after `Dealloc`), MiniRust its misalignment (it checks the alignment
    first); both are undefined behaviour;
  * a `Bool` byte other than `0` or `1` is refused (`unsupported
    mem.bool_byte`): the interpreter reads `true`, MiniRust calls it
    undefined behaviour.
  With its one allocation, `Step` is deterministic (`step_det`), so is `Exec`
  (`exec_det`), and `run` is its one resolution (`run_sound`,
  `run_complete`); a relational `Step` over every allocation MiniRust may
  pick (RM4's "chosen allocation") is not in this slice. `Step` is stated
  without the executable (v0's `Exec` was the graph of `stepCore`, which made
  `run_sound` the definition read back); the executable is held to it by
  proof.

  Reference: `crates/trust-ir/src/interpret.rs` (the semantics SemR is held
  to by `crates/trust-ir-conformance/tests/lean_exec_differential.rs`'s SemR
  tests) and `crates/trust-ir/src/binary.rs` (the format).
-/

namespace SemR

/-! ## Level R: the syntax of the fragment -/

/-- The integer types. Pointer-sized types use the module's target width;
    a targetless module keeps the 64-bit reference layout. -/
inductive IntTy where
  | i8 | i16 | i32 | i64 | i128 | isize | u8 | u16 | u32 | u64 | u128 | usize

def IntTy.code : IntTy → Nat
  | .i8 => 0 | .i16 => 1 | .i32 => 2 | .i64 => 3 | .i128 => 4 | .isize => 5
  | .u8 => 6 | .u16 => 7 | .u32 => 8 | .u64 => 9 | .u128 => 10 | .usize => 11

def IntTy.bits (pointerBits : Nat := 64) : IntTy → Nat
  | .i8 => 8 | .i16 => 16 | .i32 => 32 | .i64 => 64 | .i128 => 128 | .isize => pointerBits
  | .u8 => 8 | .u16 => 16 | .u32 => 32 | .u64 => 64 | .u128 => 128 | .usize => pointerBits

def IntTy.signed : IntTy → Bool
  | .i8 | .i16 | .i32 | .i64 | .i128 | .isize => true
  | _ => false

/-- The bytes an integer occupies in memory, also its alignment. Only
    `isize`/`usize` depend on the target; fixed-width integers retain their size. -/
def IntTy.bytes (pointerBits : Nat := 64) : IntTy → Nat
  | .i8 | .u8 => 1 | .i16 | .u16 => 2 | .i32 | .u32 => 4
  | .i64 | .u64 => 8 | .isize | .usize => pointerBits / 8 | .i128 | .u128 => 16

/-- The types of the fragment. -/
inductive Ty where
  | int (t : IntTy)
  | bool
  | ptr
  | unit
  | never
  | enum (id : Nat)
  | struct (id : Nat)
  /-- Nominal closure identity, currently available only to quoted models. -/
  | closure (id : Nat)
  /-- Geometry-only possibly-uninitialized storage; never a transported value. -/
  | storage (size align : Nat)
  /-- A tensor of integer elements and a fixed rank (`Ty::Tensor`, wire v67).
      The type fixes only the element type and the rank; each extent is a
      runtime value the tensor carries. A float element is refused by the
      decoder (`tensor.float_element`): SemR has no float model. -/
  | tensor (elem : IntTy) (rank : Nat)

def Ty.beq : Ty → Ty → Bool
  | .int a, .int b => a.code == b.code
  | .bool, .bool => true
  | .ptr, .ptr => true
  | .unit, .unit => true
  | .never, .never => true
  | .enum a, .enum b => a == b
  | .struct a, .struct b => a == b
  | .closure a, .closure b => a == b
  | .storage sa aa, .storage sb ab => sa == sb && aa == ab
  | .tensor ea ra, .tensor eb rb => ea.code == eb.code && ra == rb
  | _, _ => false

/-- Exact declaration-order type comparison, with nominal IDs retained. -/
def tyListEq : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && tyListEq as bs
  | _, _ => false

inductive BinOp where
  | add | sub | mul | udiv | sdiv | urem | srem | and | or | xor | shl | lshr | ashr
  | bAnd | bOr | bXor | rotl | rotr

inductive UnOp where
  | neg | not | ctpop | ctlz | cttz | bswap | bitreverse

inductive ICmpOp where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge

inductive OvfOp where
  | add | sub | mul

/-- The integer casts (`CastOp`'s `Trunc`, `ZExt`, `SExt`, `Bitcast`). -/
inductive CastOp where
  | trunc | zext | sext | bitcast

/-- A constant. An integer literal is its 128-bit two's-complement pattern
    (the wire's `i128`, read as unsigned). -/
inductive Const where
  | int (pattern : Nat)
  | bool (b : Bool)
  | aggregate (elems : List Const)
  /-- Only a DIRECT lane of a Struct constant, never a standalone value. -/
  | uninit
  /-- A content-addressed integer tensor (`Constant::TensorBlob`, wire v70):
      the SHA-256 of its element bytes (32 bytes) and its extents. -/
  | tensorBlob (digest : List Nat) (dims : List Nat)

/-- What a failed `Assert` panics with (`AssertKind`); the operand ids of
    `bounds` and `misaligned` are value ids. -/
inductive AssertKind where
  | unspecified
  | overflow (op : Nat)
  | divByZero
  | remByZero
  | bounds (index len : Nat)
  | misaligned (required found : Nat)
  | nullPtr

/-- One node of a tensor map's scalar body (`TensorMapNode`, wire v68): the
    scalar instruction of the same name over LANE numbers, a lane being an
    operand's element at the coordinate (or a scalar operand itself) or an
    earlier node's value. -/
inductive MapNode where
  | binop (op : BinOp) (ty : Ty) (lhs rhs : Nat)
  | unop (op : UnOp) (ty : Ty) (operand : Nat)
  | icmp (op : ICmpOp) (ty : Ty) (lhs rhs : Nat)
  | select (ty : Ty) (cond thenL elseL : Nat)
  | cast (op : CastOp) (src dst : Ty) (operand : Nat)

/-- A tensor reduction's combining operator (`TensorReduceOp`, wire v68). Its
    one fold order (`TensorReduceOrder::RowMajor`, the only tag the decoder
    admits) is not carried: it is the order `evalReduce` folds in. -/
inductive ReduceOp where
  | add | mul | and | or | xor | smin | smax | umin | umax

/-- One node of a tensor view's coordinate function (`TensorIndexExpr`, wire
    v68), an integer: a literal, a `usize` parameter, a source extent, a
    result coordinate, or arithmetic over two earlier nodes (`div`/`rem`
    Euclidean). -/
inductive IxExpr where
  | lit (n : Nat)
  | param (k : Nat)
  | srcExtent (j : Nat)
  | coord (i : Nat)
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | div (a b : Nat)
  | rem (a b : Nat)
  | min (a b : Nat)
  | max (a b : Nat)

/-- The instructions of the fragment. Value, block and frame ids are `Nat`s. -/
inductive Inst where
  | binop (op : BinOp) (ty : Ty) (lhs rhs : Nat)
  | unop (op : UnOp) (ty : Ty) (operand : Nat)
  | overflow (op : OvfOp) (ty : Ty) (lhs rhs : Nat)
  | icmp (op : ICmpOp) (ty : Ty) (lhs rhs : Nat)
  | const (ty : Ty) (c : Const)
  | copy (ty : Ty) (operand : Nat)
  | select (ty : Ty) (cond thenV elseV : Nat)
  | extractField (ty : Ty) (agg : Nat) (field : Nat)
  | insertField (ty : Ty) (agg : Nat) (field : Nat) (value : Nat)
  | undef (ty : Ty)
  | assume (cond : Nat)
  /-- Abstract, one-element private scalar cells. No byte pointer arithmetic,
      casts, globals, volatile/atomic access or deallocation is implicit. -/
  | allocaCell (ty : Ty)
  | loadCell (ty : Ty) (ptr : Nat)
  | storeCell (ty : Ty) (ptr value : Nat)
  | openFrame (slots : List Ty)
  | bindSlot (frame : Nat) (slot : Nat) (value : Nat)
  | loadSlot (frame : Nat) (slot : Nat) (ty : Ty)
  | closeFrame (frame : Nat)
  | nullPtr
  | unreachable
  | assert (cond : Nat) (kind : AssertKind)
  | call (callee : Nat) (args : List Nat)
  /-- Quoted-only runtime environment construction; not binary-decoded. -/
  | makeClosure (ty target : Nat) (captures : List Nat)
  | br (target : Nat) (args : List Nat)
  | condBr (cond : Nat) (thenT : Nat) (thenArgs : List Nat) (elseT : Nat) (elseArgs : List Nat)
  | ret (values : List Nat)
  | cast (op : CastOp) (src dst : Ty) (operand : Nat)
  | switch (value : Nat) (default : Nat) (defaultArgs : List Nat) (cases : List (Const × Nat × List Nat))
  | alloca (ty : Ty) (count : Option Nat) (align : Option Nat)
  | load (ty : Ty) (ptr : Nat) (volatile : Bool) (align : Option Nat)
  | store (ty : Ty) (ptr : Nat) (value : Nat) (volatile : Bool) (align : Option Nat)
  | gep (pointee : Ty) (base : Nat) (indices : List Nat)
  | dealloc (ptr : Nat)
  /-- `Inst::TensorContract` (XLA's DotGeneral): batch and contracted axis
      pairs `(lhs axis, rhs axis)`; the result is a tensor of type `ty`. -/
  | tensorContract (ty : Ty) (lhs rhs : Nat) (batch contract : List (Nat × Nat))
  /-- `Inst::TensorMap` (v68): the scalar `body` at every coordinate of the
      tensor operands among `args`; the last node's value is the element. -/
  | tensorMap (ty : Ty) (args : List Nat) (body : List MapNode)
  /-- `Inst::TensorReduce` (v68): `src` folded by `op` along `axes`, in
      row-major order (`TensorReduceOrder::RowMajor`). -/
  | tensorReduce (ty : Ty) (src : Nat) (op : ReduceOp) (axes : List Nat)
  /-- `Inst::TensorView` (v68): the result's extents are the `shape` nodes,
      each element the source element at the `index` nodes' coordinate, or
      the `fill` operand where that coordinate is out of range. -/
  | tensorView (ty : Ty) (src : Nat) (params : List Nat) (exprs : List IxExpr)
      (shape index : List Nat) (fill : Option Nat)
  /-- `Inst::TensorGather` (v69): the result's extents are the coordinate
      tensors', each element `data`'s at the coordinate the `coords` (one
      per data axis, in axis order) hold at that position. -/
  | tensorGather (ty : Ty) (data : Nat) (coords : List Nat)
  /-- `Inst::TensorScatter` (v69): `init` with `src`'s element at each
      source position written, in row-major order, at the coordinate the
      `coords` (one per axis of `init`, in axis order) hold there; the
      row-major-last write at a repeated coordinate wins. -/
  | tensorScatter (ty : Ty) (init src : Nat) (coords : List Nat)

structure Node where
  inst : Inst
  results : List Nat

structure Block where
  id : Nat
  params : List (Nat × Ty)
  body : List Node

structure FuncTy where
  params : List Ty
  returns : List Ty
  vararg : Bool

/-- A nominal closure declaration. Its callable target has the capture types
    followed by the apparent parameters, and the apparent return types. -/
structure ClosureTy where
  func : Nat
  captures : List Ty

/-- A function: its id, signature index, entry block and blocks, and its
    symbol (`Function.name`, the UTF-8 bytes of the string the record names,
    the mangled path a row's function is identified by; no run reads it). -/
structure Func where
  id : Nat
  ty : Nat
  entry : Nat
  blocks : List Block
  name : List Nat := []

structure Variant where
  fields : List Ty

/-- An enum definition: its variants, each variant's EFFECTIVE discriminant
    (`EnumDef::effective_discriminants`: explicit, or one more than the
    previous, the first `0`) and the canonical tag type the tag lane carries
    (`EnumDef::canonical_tag_repr`: the `repr` hint, or the smallest width over
    the discriminants' range). An enum with no explicit discriminant, no
    `repr` and no layout record has `discs = [0, …, n-1]` and tag `u8`
    (`n ≤ 256`), as in v0; one with any of the three is decoded only when it
    is fieldless (D-2(b)). -/
structure EnumDef where
  id : Nat
  variants : List Variant
  discs : List Int
  tag : IntTy

structure StructDef where
  id : Nat
  fields : List Ty

/-- Exact target metadata: strings retain their validated UTF-8 bytes, including
    the ABI and the aggregate classification. Neither grants ABI authority. -/
structure TargetInfo where
  triple : List Nat
  pointerSize : Nat
  bigEndian : Bool
  abi : Option (List Nat)
  structPassing : Nat

structure Module where
  funcTys : List FuncTy
  enums : List EnumDef
  functions : List Func
  target : Option TargetInfo := none
  /-- Flat scalar logical structs may also come from canonical bytes. Physical
      layouts, nominal-origin records and private-cell instructions remain refused. -/
  structs : List StructDef := []
  /-- Quoted-only nominal environment table. The binary decoder still requires
      the canonical closure_types section to be empty. -/
  closures : List ClosureTy := []
  /-- The content-addressed blob table (wire v70): each row a 32-byte digest
      and the bytes it names, strictly ascending by digest. -/
  blobs : List (List Nat × List Nat) := []

def Module.pointerBits (m : Module) : Nat :=
  match m.target with
  | none => 64
  | some t => 8 * t.pointerSize

/-- The same canonical scalar-table selection as
    `Module::target_has_canonical_scalar_layout` and the interpreter's
    `require_reference_execution_layout`. A triple alone never guesses a layout. -/
def Module.executableTarget (m : Module) : Bool :=
  match m.target with
  | none => true
  | some t =>
    let arch := t.triple.takeWhile (· != 45)
    let bytes := fun (s : String) => s.toList.map Char.toNat
    !t.bigEndian &&
      ((t.pointerSize == 8 &&
        (arch == bytes "x86_64" || arch == bytes "x64" || arch == bytes "aarch64" ||
         arch == bytes "arm64" || arch == bytes "wasm64" || (bytes "riscv64").isPrefixOf arch)) ||
       (t.pointerSize == 4 && arch == bytes "wasm32"))

/-! ## Values -/

/-- A byte of memory (MiniRust's `AbstractByte`): uninitialized, or
    initialized to `b < 256`. MiniRust's byte also carries a provenance
    fragment for the bytes of a stored pointer; this slice stores no pointer
    (a pointer-typed `Load`/`Store` is `unsupported mem.access.ty`), so no byte
    it writes has one. -/
inductive AByte where
  | uninit
  | init (b : Nat)

/-- A runtime value. Every integer is its residue in `[0, 2^bits)`. An enum
    value is `[tag, fields…]`, the tag an integer of the enum's tag type whose
    residue is the active variant's discriminant. A frame handle is its
    lineage and its own slot snapshot (`None`: unbound). `poison ty` is the
    scalar poison an unbound `LoadSlot` reads (the interpreter's
    `PartialBytes`): it may be copied, selected and branched with, never
    inspected. `ptr alloc offset` is a pointer with provenance (MiniRust's
    `ThinPointer` with `Some` provenance, the interpreter's `Ptr`): the
    allocation it was derived from and its byte offset in it. `partialBytes ty
    bytes` is the poison a plain scalar `Load` of partly uninitialized memory
    reads, its bytes kept (the interpreter's `PartialBytes`): like `poison`,
    it may be moved and stored, never inspected. -/
inductive Val where
  | int (t : IntTy) (raw : Nat)
  | bool (b : Bool)
  | nullPtr
  | enum (id : Nat) (lanes : List Val)
  | struct (id : Nat) (lanes : List Val)
  /-- Original capture values, including exact allocation/offset provenance. -/
  | closure (id target : Nat) (captures : List Val)
  /-- A stable logical identity, never a machine address or a binding frame. -/
  | cellPtr (id : Nat)
  | unwritten (ty : Ty)
  | frame (lineage : Nat) (slots : List (Option Val))
  | poison (ty : Ty)
  | ptr (alloc : Nat) (offset : Nat)
  | partialBytes (ty : Ty) (bytes : List AByte)
  /-- A tensor value: its element type, its extents (rank = their count) and
      its elements in row-major order (last axis fastest), each a residue. -/
  | tensor (elem : IntTy) (dims : List Nat) (elems : List Nat)

/-- The type a value carries (the interpreter's `InterpretValue::ty`). A frame
    handle is a `ptr`. -/
def Val.ty : Val → Ty
  | .int t _ => .int t
  | .bool _ => .bool
  | .nullPtr => .ptr
  | .enum id _ => .enum id
  | .struct id _ => .struct id
  | .closure id _ _ => .closure id
  | .cellPtr _ => .ptr
  | .unwritten ty => ty
  | .frame _ _ => .ptr
  | .poison t => t
  | .ptr _ _ => .ptr
  | .partialBytes t _ => t
  | .tensor e dims _ => .tensor e dims.length

/-! ## The scalar operator layer (on residues) -/

/-- `2^w`. -/
def modulus (w : Nat) : Nat := 2 ^ w

/-- The sign bit's weight, `2^(w-1)`. -/
def half (w : Nat) : Nat := 2 ^ (w - 1)

/-- The residue is negative as a signed `w`-bit value. -/
def isNeg (w a : Nat) : Bool := decide (half w ≤ a)

/-- The magnitude of the signed reading of residue `a`. -/
def mag (w a : Nat) : Nat := if isNeg w a then modulus w - a else a

/-- The residue of `-x` for a magnitude `x`. -/
def negR (w x : Nat) : Nat := (modulus w - x % modulus w) % modulus w

def wrap (w x : Nat) : Nat := x % modulus w

/-- The outcome of one operator: a value, undefined behaviour, or a type
    error (an operation the type does not admit). -/
inductive OpRes (α : Type) where
  | ok (a : α)
  | ub (msg : String)
  | tyErr (msg : String)
  | unsup (feature : String)

def popcount : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, a => a % 2 + popcount w (a / 2)

/-- Leading zeros of the `w`-bit residue: peels the top bit. -/
def ctlzW (a : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => if (a / 2 ^ w) % 2 == 1 then 0 else 1 + ctlzW a w

/-- Trailing zeros of the `w`-bit residue: peels the bottom bit. -/
def cttzW : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, a => if a % 2 == 1 then 0 else 1 + cttzW w (a / 2)

def bitrevW : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, a => (a % 2) * 2 ^ w + bitrevW w (a / 2)

def bswapN : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a => (a % 256) * 256 ^ n + bswapN n (a / 256)

/-- `BinOp` on two `w`-bit residues (`eval_int_binop`). -/
def intBin (op : BinOp) (w a b : Nat) : OpRes Nat :=
  let m := modulus w
  match op with
  | .add => .ok ((a + b) % m)
  | .sub => .ok ((a + (m - b % m)) % m)
  | .mul => .ok ((a * b) % m)
  | .and => .ok (Nat.land a b % m)
  | .or => .ok (Nat.lor a b % m)
  | .xor => .ok (Nat.xor a b % m)
  | .bAnd => .ok (if a != 0 && b != 0 then 1 else 0)
  | .bOr => .ok (if a != 0 || b != 0 then 1 else 0)
  | .bXor => .ok (if (a != 0) != (b != 0) then 1 else 0)
  | .udiv => if b == 0 then .ub "unsigned division by zero" else .ok (a / b)
  | .urem => if b == 0 then .ub "unsigned remainder by zero" else .ok (a % b)
  | .sdiv =>
    if b == 0 then .ub "signed division by zero"
    else if a == half w && b == m - 1 then .ub "signed division overflow"
    else
      let q := mag w a / mag w b
      .ok (if isNeg w a != isNeg w b then negR w q else q % m)
  | .srem =>
    if b == 0 then .ub "signed remainder by zero"
    else if a == half w && b == m - 1 then .ub "signed remainder overflow"
    else
      let r := mag w a % mag w b
      .ok (if isNeg w a then negR w r else r % m)
  | .shl => if w ≤ b then .ub "shift amount out of range" else .ok ((a * 2 ^ b) % m)
  | .lshr => if w ≤ b then .ub "shift amount out of range" else .ok (a / 2 ^ b)
  | .ashr =>
    if w ≤ b then .ub "shift amount out of range"
    else .ok (a / 2 ^ b + (if isNeg w a then m - 2 ^ (w - b) else 0))
  | .rotl => let n := b % w; .ok ((a * 2 ^ n) % m + a / 2 ^ (w - n))
  | .rotr => let n := b % w; .ok (a / 2 ^ n + (a * 2 ^ (w - n)) % m)

/-- `BinOp` on two `Bool`s (`eval_bool_binop`). -/
def boolBin (op : BinOp) (a b : Bool) : OpRes Bool :=
  match op with
  | .and | .bAnd => .ok (a && b)
  | .or | .bOr => .ok (a || b)
  | .xor | .bXor => .ok (a != b)
  | _ => .tyErr "not a boolean binary operation"

/-- Integer `UnOp` (`eval_int_unop`). -/
def intUn (op : UnOp) (w a : Nat) : Nat :=
  match op with
  | .neg => negR w a
  | .not => modulus w - 1 - a % modulus w
  | .ctpop => popcount w a
  | .ctlz => ctlzW a w
  | .cttz => cttzW w a
  | .bswap => bswapN (w / 8) a
  | .bitreverse => bitrevW w a

/-- The residue ordered as a signed value: bias by the sign bit. -/
def biased (w a : Nat) : Nat := (a + half w) % modulus w

def icmpR (op : ICmpOp) (w a b : Nat) : Bool :=
  match op with
  | .eq => a == b
  | .ne => a != b
  | .ult => decide (a < b)
  | .ule => decide (a ≤ b)
  | .ugt => decide (b < a)
  | .uge => decide (b ≤ a)
  | .slt => decide (biased w a < biased w b)
  | .sle => decide (biased w a ≤ biased w b)
  | .sgt => decide (biased w b < biased w a)
  | .sge => decide (biased w b ≤ biased w a)

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- The checked trio: the wrapped value and the overflow flag against the
    operands' signedness (`eval_int_overflow`). -/
def ovf (op : OvfOp) (signed : Bool) (w a b : Nat) : Nat × Bool :=
  let m := modulus w
  match op with
  | .add =>
    let r := (a + b) % m
    (r, if signed then isNeg w a == isNeg w b && isNeg w r != isNeg w a
        else decide (m ≤ a + b))
  | .sub =>
    let r := (a + (m - b % m)) % m
    (r, if signed then isNeg w a != isNeg w b && isNeg w r != isNeg w a
        else decide (a < b))
  | .mul =>
    let r := (a * b) % m
    let p := mag w a * mag w b
    (r, if signed then
          (if isNeg w a != isNeg w b then decide (half w < p) else decide (half w ≤ p))
        else decide (m ≤ a * b))

/-! ## Results of a step -/

/-- The verdict of a run, the oracle grammar of `TrustIrEval/Run.lean`. -/
inductive Out where
  | ret (vs : List Val)
  | ub (msg : String)
  | typeError (msg : String)
  | unsupported (feature : String)
  | outOfFuel
  | panic (msg : String)
  | outOfMemory

/-- A computation that either continues with a value or stops with a verdict. -/
inductive R (α : Type) where
  | ok (a : α)
  | stop (o : Out)

def R.bind {α β : Type} (x : R α) (f : α → R β) : R β :=
  match x with
  | .ok a => f a
  | .stop o => .stop o

def R.map {α β : Type} (f : α → β) (x : R α) : R β :=
  match x with
  | .ok a => .ok (f a)
  | .stop o => .stop o

/-- Every field spelled: Clean's elaborator does not fill a parent's
    defaulted fields (`mapConst`, `seq`, …). -/
instance : Monad R where
  pure := R.ok
  bind := R.bind
  map := R.map
  mapConst := fun a x => R.map (fun _ => a) x
  seq := fun f x => R.bind f (fun g => R.map g (x ()))
  seqLeft := fun x y => R.bind x (fun a => R.map (fun _ => a) (y ()))
  seqRight := fun x y => R.bind x (fun _ => y ())

def ubR {α : Type} (msg : String) : R α := .stop (.ub msg)
def tyR {α : Type} (msg : String) : R α := .stop (.typeError msg)
def unsupR {α : Type} (f : String) : R α := .stop (.unsupported f)

def liftOp {α : Type} : OpRes α → R α
  | .ok a => .ok a
  | .ub m => .stop (.ub m)
  | .tyErr m => .stop (.typeError m)
  | .unsup f => .stop (.unsupported f)

/-! ## The machine -/

/-- One allocation (MiniRust's `Allocation`): its address, its size and
    alignment, whether it is live, and its bytes. `data` holds a prefix of the
    allocation's bytes; every byte past it is uninitialized (a fresh
    allocation's `data` is `[]`), so an allocation of any size costs nothing
    until it is written (the interpreter's sparse `ByteStore`). -/
structure Alloc where
  base : Nat
  size : Nat
  align : Nat
  live : Bool
  data : List AByte

/-- The memory (MiniRust's `BasicMemory`): the allocations, an allocation's
    id its position (MiniRust's `AllocId`, the interpreter's sequential
    `next_alloc_id`), and the next free address of the interpreter's bump
    allocator (`MemoryState::next_addr`, `1024` at the start of a run). No
    allocation is ever removed: `Dealloc` marks it dead, so a stale pointer
    keeps naming it. -/
structure Mem where
  allocs : List Alloc
  nextAddr : Nat

/-- The memory a run starts with. -/
def Mem.empty : Mem := { allocs := [], nextAddr := 1024 }

/-- A suspended caller: its position, its environment, its remaining call
    depth, and the call node whose results the callee's return binds. -/
structure Caller where
  fn : Func
  sig : FuncTy
  block : Block
  pc : Nat
  env : List (Nat × Val)
  depth : Nat
  node : Node

/-- A typed private scalar cell. Its poison/initialized content is shared by
    every alias, including suspended callers; a pointer carries no snapshot. -/
structure Cell where
  id : Nat
  ty : Ty
  value : Val

/-- The execution state. `fn`/`sig`/`block`/`pc`/`env` are the running body
    (`env` its SSA environment, latest binding first, private to the call as
    the interpreter's swapped `values` map is), `depth` the call depth left
    (`ensure_call_depth`), `stack` the suspended callers, `openFrames` /
    `nextFrame` the binding-frame lineages, and `mem` the memory; the last
    three are shared by every call (a `Return` frees nothing: trust-ir's
    level R deallocates a stack slot only by an explicit `Dealloc`, the
    producer's `StorageDead`). -/
structure Core where
  fn : Func
  sig : FuncTy
  block : Block
  pc : Nat
  env : List (Nat × Val)
  depth : Nat
  stack : List Caller
  openFrames : List Nat
  nextFrame : Nat
  cells : List Cell := []
  nextCell : Nat := 0
  mem : Mem

def lookupEnv : List (Nat × Val) → Nat → Option Val
  | [], _ => none
  | (k, v) :: rest, x => if k == x then some v else lookupEnv rest x

def getV (k : Core) (x : Nat) : R Val :=
  match lookupEnv k.env x with
  | some v => .ok v
  | none => tyR "MissingValue: value is not defined"

def getVs (k : Core) : List Nat → R (List Val)
  | [] => .ok []
  | x :: xs => do let v ← getV k x; let vs ← getVs k xs; pure (v :: vs)

/-- `reject_partial`: inspecting poison is undefined behaviour. -/
def rejectPoison (v : Val) (what : String) : R Unit :=
  match v with
  | .poison _ => ubR s!"{what}: use of an uninitialized value (poison)"
  | .unwritten _ => ubR s!"{what}: use of an unwritten aggregate lane (uninit)"
  | .partialBytes _ _ => ubR s!"{what}: use of an uninitialized value (poison)"
  | _ => .ok ()

/-- `expect_ty`: the value's type is exactly `t`. -/
def expectTy (pointerBits : Nat) (v : Val) (t : Ty) : R Unit :=
  if (match t with | .storage _ _ => true | _ => false) then
    tyR "TypeError: storage-only type has no value"
  else if !v.ty.beq t then tyR "TypeError: value does not have the expected type"
  else match v with
    | .int it raw =>
      if raw < modulus (it.bits pointerBits) then .ok ()
      else tyR "TypeError: integer value is out of range for the target width"
    | _ => .ok ()

/-- Re-express a self-described embedder integer at the module's target width,
    as `narrow_pointer_width_ints` does before entry. Signed inputs preserve
    their mathematical value, never their old unsigned residue or a truncated
    out-of-range value. Internal values already use the target's width. -/
def entryInt (m : Module) (t : IntTy) (sourceBits raw : Nat) : R Val := do
  if sourceBits == 0 || 128 < sourceBits then
    tyR "TypeError: invalid entry integer width"
  else if modulus sourceBits ≤ raw then
    tyR "TypeError: invalid entry integer representation"
  else
    let w := t.bits m.pointerBits
    if t.code != IntTy.isize.code && t.code != IntTy.usize.code then
      if sourceBits == w then pure (.int t raw)
      else tyR "TypeError: entry integer width does not match its type"
    else if t.signed && isNeg sourceBits raw then
      let magnitude := modulus sourceBits - raw
      if magnitude ≤ half w then pure (.int t (negR w magnitude))
      else tyR "TypeError: signed entry argument is out of range for the target width"
    else
      let bound := if t.signed then half w else modulus w
      if raw < bound then pure (.int t raw)
      else tyR "TypeError: entry argument is out of range for the target width"

def expectInt (v : Val) : R (IntTy × Nat) := do
  rejectPoison v "integer use"
  match v with
  | .int t a => pure (t, a)
  | _ => tyR "TypeError: expected integer value"

def expectBool (v : Val) : R Bool := do
  rejectPoison v "bool use"
  match v with
  | .bool b => pure b
  | _ => tyR "TypeError: expected bool value"

def isBoolTy : Ty → Bool
  | .bool => true
  | _ => false

def evalBinop (pointerBits : Nat) (op : BinOp) (ty : Ty) (a b : Val) : R Val := do
  expectTy pointerBits a ty
  expectTy pointerBits b ty
  if isBoolTy ty then
    let x ← expectBool a
    let y ← expectBool b
    let r ← liftOp (boolBin op x y)
    pure (.bool r)
  else
    let (t, x) ← expectInt a
    let (_, y) ← expectInt b
    let r ← liftOp (intBin op (t.bits pointerBits) x y)
    pure (.int t r)

/-- A scalar `UnOp` is integer-only: on a `Bool` operand `expect_int_value`
    is a type error (the interpreter's scalar arm). -/
def evalUnop (pointerBits : Nat) (op : UnOp) (ty : Ty) (a : Val) : R Val := do
  expectTy pointerBits a ty
  let (t, x) ← expectInt a
  pure (.int t (intUn op (t.bits pointerBits) x))

def evalIcmp (pointerBits : Nat) (op : ICmpOp) (ty : Ty) (a b : Val) : R Val := do
  expectTy pointerBits a ty
  expectTy pointerBits b ty
  if isBoolTy ty then
    let x ← expectBool a
    let y ← expectBool b
    pure (.bool (icmpR op 1 (b2n x) (b2n y)))
  else
    let (t, x) ← expectInt a
    let (_, y) ← expectInt b
    pure (.bool (icmpR op (t.bits pointerBits) x y))

def evalOverflow (pointerBits : Nat) (op : OvfOp) (ty : Ty) (a b : Val) : R (List Val) := do
  expectTy pointerBits a ty
  expectTy pointerBits b ty
  let (t, x) ← expectInt a
  let (_, y) ← expectInt b
  let (r, f) := ovf op t.signed (t.bits pointerBits) x y
  pure [.int t r, .bool f]

def findEnum : List EnumDef → Nat → Option EnumDef
  | [], _ => none
  | d :: ds, id => if d.id == id then some d else findEnum ds id

def findStruct : List StructDef → Nat → Option StructDef
  | [], _ => none
  | d :: ds, id => if d.id == id then some d else findStruct ds id

def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth? as n

def setNth {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: as, 0, b => b :: as
  | a :: as, n + 1, b => a :: setNth as n b

/-- Pairwise over two lists, stopping at the first verdict; the shorter list
    ends it (the caller checks the lengths first). -/
def mapM2 {α β γ : Type} (f : α → β → R γ) : List α → List β → R (List γ)
  | a :: as, b :: bs => do
    let c ← f a b
    let cs ← mapM2 f as bs
    pure (c :: cs)
  | _, _ => .ok []

/-- The placement guard is bounded together with constant materialization;
    exhausted depth refuses rather than overlooking a hidden Uninit. -/
def containsUninit : Nat → Const → Bool
  | 0, _ => true
  | _ + 1, .uninit => true
  | fuel + 1, .aggregate xs => xs.any (containsUninit fuel)
  | _ + 1, _ => false
/-- Whether a constant is or holds a `Const.tensorBlob` within `fuel` levels
    (the levels `constVal` reads: past them it is `unsupported` anyway). -/
def containsBlob : Nat → Const → Bool
  | 0, _ => false
  | _ + 1, .tensorBlob _ _ => true
  | fuel + 1, .aggregate xs => xs.any (containsBlob fuel)
  | _ + 1, _ => false
/-- The `w`-bit residue of an integer (`InterpretValue::int`'s mask). -/
def resid (w : Nat) : Int → Nat
  | .ofNat n => n % modulus w
  | .negSucc n => negR w (n + 1)

/-- The value a `w`-bit residue denotes under the signedness `s`
    (`tag_int_discriminant`). -/
def readInt (s : Bool) (w a : Nat) : Int :=
  if s && isNeg w a then (a : Int) - (modulus w : Int) else (a : Int)

/-- The position of `x` in `xs` (`Iterator::position`). -/
def posOf : List Int → Int → Option Nat
  | [], _ => none
  | y :: ys, x => if y == x then some 0 else (posOf ys x).map (· + 1)

/-- The signed reading of a 128-bit constant pattern (the wire's `i128`). -/
def i128Of (p : Nat) : Int := readInt true 128 p

/-! ### Content-addressed blobs (wire v70)

FIPS 180-4 SHA-256 over a byte list, on `Nat` words below `2^32`
(`Nat.land`/`lor`/`xor` and the shifts, which the kernel computes), and the
tensor a `Const.tensorBlob` names. -/

/-- The product of extents: a row-major tensor's element count. -/
def prodL : List Nat → Nat
  | [] => 1
  | d :: ds => d * prodL ds

/-- Residue `i` of an element list (`0` past its end, which a well-formed
    operand is never read at). -/
def getN : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, n + 1 => getN as n

/-- `2^32`, the SHA-256 word modulus. -/
def shaM : Nat := 4294967296

def shaAdd (a b : Nat) : Nat := (a + b) % shaM

/-- Rotate a word right by `n` (`0 < n < 32`). -/
def shaRotr (x n : Nat) : Nat := Nat.lor (x >>> n) ((x <<< (32 - n)) % shaM)

def shaK : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value, eight words `a … h`. -/
def shaH0 : List Nat :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- One compression round over the working words `[a, b, c, d, e, f, g, h]`. -/
def shaRound (s : List Nat) (k w : Nat) : List Nat :=
  match s with
  | [a, b, c, d, e, f, g, h] =>
    let t1 := shaAdd (shaAdd (shaAdd (shaAdd h
      (Nat.xor (Nat.xor (shaRotr e 6) (shaRotr e 11)) (shaRotr e 25)))
      (Nat.xor (Nat.land e f) (Nat.land (shaM - 1 - e) g))) k) w
    let t2 := shaAdd (Nat.xor (Nat.xor (shaRotr a 2) (shaRotr a 13)) (shaRotr a 22))
      (Nat.xor (Nat.xor (Nat.land a b) (Nat.land a c)) (Nat.land b c))
    [shaAdd t1 t2, a, b, c, shaAdd d t1, e, f, g]
  | _ => s

/-- A block's sixteen big-endian words. -/
def shaWords : List Nat → List Nat
  | a :: b :: c :: d :: rest => (a * 16777216 + b * 65536 + c * 256 + d) :: shaWords rest
  | _ => []

/-- The message schedule's next `n` words after the sixteen-word window `w`
    (oldest first). -/
def shaSchedule : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, w =>
    let x := getN w 14
    let y := getN w 1
    let next := shaAdd (shaAdd (shaAdd
      (Nat.xor (Nat.xor (shaRotr x 17) (shaRotr x 19)) (x >>> 10)) (getN w 9))
      (Nat.xor (Nat.xor (shaRotr y 7) (shaRotr y 18)) (y >>> 3))) (getN w 0)
    next :: shaSchedule n (w.drop 1 ++ [next])

def shaRounds : List Nat → List Nat → List Nat → List Nat
  | k :: ks, w :: ws, s => shaRounds ks ws (shaRound s k w)
  | _, _, s => s

/-- One 64-byte block folded into the hash value `h`. -/
def shaBlock (h : List Nat) (chunk : List Nat) : List Nat :=
  let ws := shaWords chunk
  let s := shaRounds shaK (ws ++ shaSchedule 48 ws) h
  (List.zip h s).map (fun p => shaAdd p.1 p.2)

def shaBlocks : Nat → List Nat → List Nat → List Nat
  | 0, h, _ => h
  | n + 1, h, bs => shaBlocks n (shaBlock h (bs.take 64)) (bs.drop 64)

/-- `n` big-endian bytes of `x`. -/
def beBytes : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => beBytes n (x / 256) ++ [x % 256]

/-- FIPS 180-4 §5.1.1: a one bit, zeros to 56 mod 64, the 64-bit bit length. -/
def shaPad (msg : List Nat) : List Nat :=
  msg ++ [128] ++ List.replicate ((119 - msg.length % 64) % 64) 0 ++ beBytes 8 (8 * msg.length)

/-- The SHA-256 digest of a byte list: 32 bytes. -/
def sha256 (msg : List Nat) : List Nat :=
  let p := shaPad msg
  (shaBlocks (p.length / 64) shaH0 p).flatMap (beBytes 4)

/-- Two byte lists of one length, compared lexicographically. -/
def bytesLt : List Nat → List Nat → Bool
  | a :: as, b :: bs => if a == b then bytesLt as bs else decide (a < b)
  | _, _ => false

/-- The first blob table row keyed by `d` (`Module::blob`). -/
def blobRow : List (List Nat × List Nat) → List Nat → Option (List Nat)
  | [], _ => none
  | (k, bytes) :: rows, d => if k == d then some bytes else blobRow rows d

/-- `n` little-endian bytes as a number. -/
def leNat : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * leNat bs

/-- `n` elements of `w` bytes each, read little-endian. -/
def leChunks (w : Nat) : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, bs => leNat (bs.take w) :: leChunks w n (bs.drop w)

/-- `tensor_blob_value`: the tensor a `Const.tensorBlob` names, checked in the
    reference interpreter's order, each failure a type error. -/
def blobVal (m : Module) (e : IntTy) (r : Nat) (d dims : List Nat) : R Val :=
  if dims.length != r then tyR "TypeError: tensor blob constant rank" else
  if !(dims.all (fun x => decide (x < modulus m.pointerBits))) then
    tyR "TypeError: tensor blob constant extent outside usize" else
  match blobRow m.blobs d with
  | none => tyR "TypeError: tensor blob constant names no blob"
  | some bytes =>
    if sha256 bytes != d then tyR "TypeError: tensor blob bytes do not hash to the digest" else
    let w := e.bytes m.pointerBits
    let n := prodL dims
    if !(decide (n < modulus m.pointerBits) && n * w == bytes.length) then
      tyR "TypeError: tensor blob byte count" else
    .ok (.tensor e dims (leChunks w n bytes))

/-- FIPS 180-4's examples: the empty message and `abc` (one block each),
    checked by the kernel. -/
theorem sha256_vectors :
    sha256 [] = [0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8,
      0x99, 0x6f, 0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95,
      0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55] ∧
    sha256 [97, 98, 99] = [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41,
      0x40, 0xde, 0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
      0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad] := by decide +kernel

/-- A module holding the one blob `bytes`. -/
def blobModule (bytes : List Nat) : Module :=
  { funcTys := [], enums := [], functions := [], blobs := [(sha256 bytes, bytes)] }

/-- Whether `r` is the type error `msg`. -/
def isTypeError (r : R Val) (msg : String) : Bool :=
  match r with
  | .stop (.typeError m) => m == msg
  | _ => false

/-- A `u16` pair read little-endian; a missing row, bytes that do not hash to
    the digest, a byte count the extents do not describe and a rank other
    than the type's are type errors (checked by the kernel). -/
theorem blobVal_reads_and_refuses :
    (match blobVal (blobModule [1, 0, 2, 1]) .u16 1 (sha256 [1, 0, 2, 1]) [2] with
      | .ok (.tensor .u16 [2] [1, 258]) => true
      | _ => false) = true ∧
    isTypeError (blobVal (blobModule [1, 0, 2, 1]) .u16 1 (sha256 [1, 0]) [2])
      "TypeError: tensor blob constant names no blob" = true ∧
    isTypeError (blobVal { blobModule [1, 0, 2, 1] with
        blobs := [(sha256 [1, 0, 2, 1], [1, 0, 2, 2])] } .u16 1 (sha256 [1, 0, 2, 1]) [2])
      "TypeError: tensor blob bytes do not hash to the digest" = true ∧
    isTypeError (blobVal (blobModule [1, 0, 2, 1]) .u8 1 (sha256 [1, 0, 2, 1]) [2])
      "TypeError: tensor blob byte count" = true ∧
    isTypeError (blobVal (blobModule [1, 0, 2, 1]) .u16 2 (sha256 [1, 0, 2, 1]) [2])
      "TypeError: tensor blob constant rank" = true := by decide +kernel

/-- A constant at a type (`constant_to_value`). `fuel` bounds the nesting. -/
def constVal (m : Module) : Nat → Ty → Const → R Val
  | 0, _, _ => unsupR "constant.depth"
  | _ + 1, .int t, .int p => .ok (.int t (p % modulus (t.bits m.pointerBits)))
  | _ + 1, .bool, .bool b => .ok (.bool b)
  | _ + 1, .ptr, .int p => if p == 0 then .ok .nullPtr else tyR "TypeError: nonzero integer at ptr"
  | fuel + 1, .enum id, .aggregate (.int p :: fs) =>
    if fs.any (containsUninit fuel) then tyR "TypeError: misplaced uninit constant" else
    if fs.any (containsBlob fuel) then tyR "TypeError: misplaced tensor blob constant" else
    match findEnum m.enums id with
    | none => tyR "TypeError: enum id not found in module"
    | some d =>
      match posOf d.discs (i128Of p) with
      | none => tyR "TypeError: discriminant does not name a variant"
      | some i =>
        match nth? d.variants i with
        | none => tyR "TypeError: discriminant does not name a variant"
        | some v =>
          if fs.length != v.fields.length then tyR "TypeError: enum constant payload arity"
          else do
            let ls ← mapM2 (constVal m fuel) v.fields fs
            pure (.enum id (.int d.tag (resid (d.tag.bits m.pointerBits) (i128Of p)) :: ls))
  | fuel + 1, .struct id, .aggregate fs =>
    match findStruct m.structs id with
    | none => tyR "TypeError: struct id not found in module"
    | some d =>
      if fs.length != d.fields.length then tyR "TypeError: struct constant arity"
      else if fs.any (fun c => match c with
        | .uninit => false
        | _ => containsUninit fuel c) then tyR "TypeError: misplaced uninit constant"
      else if fs.any (containsBlob fuel) then tyR "TypeError: misplaced tensor blob constant"
      else do
        let ls ← mapM2 (fun ty c => match c with
          | .uninit => pure (.unwritten ty)
          | _ => constVal m fuel ty c) d.fields fs
        pure (.struct id ls)
  | _ + 1, .tensor e r, .tensorBlob d dims => blobVal m e r d dims
  | _ + 1, _, _ => unsupR "constant.shape"

/-- The declared field types of the variant an enum value's tag names
    (`enum_active_variant`). -/
def activeFields (m : Module) (id : Nat) (lanes : List Val) : R (List Ty) :=
  match findEnum m.enums id with
  | none => tyR "TypeError: enum id not found in module"
  | some d =>
    match lanes with
    | .int t tag :: _ =>
      match posOf d.discs (readInt t.signed (t.bits m.pointerBits) tag) with
      | some i =>
        match nth? d.variants i with
        | some v => .ok v.fields
        | none => tyR "TypeError: enum tag names no variant"
      | none => tyR "TypeError: enum tag names no variant"
    | _ => tyR "TypeError: enum value has no integer tag lane"

/-- `check_enum_payload_lane`: lane `field ≥ 1` of the active variant has type
    `t`, else undefined behaviour. -/
def checkLane (m : Module) (id : Nat) (lanes : List Val) (field : Nat) (t : Ty) : R Unit := do
  let fs ← activeFields m id lanes
  match nth? fs (field - 1) with
  | some lt => if lt.beq t then pure () else ubR "enum lane belongs to no field of the active variant"
  | none => ubR "enum lane belongs to no field of the active variant"

def evalExtract (m : Module) (ty : Ty) (agg : Val) (field : Nat) : R Val := do
  rejectPoison agg "extract_field"
  match agg with
  | .enum id lanes =>
    if 1 ≤ field then checkLane m id lanes field ty else pure ()
    match nth? lanes field with
    | none => ubR "field is out of bounds"
    | some v => do expectTy m.pointerBits v ty; pure v
  | .struct id lanes =>
    match findStruct m.structs id with
    | none => tyR "TypeError: struct id not found in module"
    | some d =>
      if lanes.length != d.fields.length then tyR "TypeError: struct lane arity"
      else match nth? d.fields field, nth? lanes field with
      | some declared, some v => do
        if !declared.beq ty then tyR "TypeError: struct field type mismatch"
        else do
          match v with
          | .unwritten _ => ubR "extract_field: read of an unwritten aggregate lane (uninit)"
          | _ => do expectTy m.pointerBits v ty; pure v
      | _, _ => ubR "field is out of bounds"
  | .closure _ _ captures =>
    -- A non-dyn closure's fields are only its capture values. Its code
    -- identity has no field or stored lane; construction checked the types.
    -- Match the interpreter: bounds, unwritten-lane and result-type checks
    -- apply to the selected value, without invoking or looking up the target.
    match nth? captures field with
    | none => ubR "field is out of bounds"
    | some v =>
      match v with
      | .unwritten _ => ubR "extract_field: read of an unwritten aggregate lane (uninit)"
      | _ => do expectTy m.pointerBits v ty; pure v
  | _ => tyR "TypeError: extract_field requires an aggregate"

def evalInsert (m : Module) (ty : Ty) (agg : Val) (field : Nat) (v : Val) : R Val := do
  rejectPoison agg "insert_field"
  rejectPoison v "insert_field value"
  expectTy m.pointerBits agg ty
  match agg with
  | .enum id lanes =>
    if field == 0 then ubR "insert_field cannot rewrite an enum discriminant"
    else do
      checkLane m id lanes field v.ty
      match nth? lanes field with
      | none => ubR "field is out of bounds"
      | some old => do
        expectTy m.pointerBits v old.ty
        pure (.enum id (setNth lanes field v))
  | .struct id lanes =>
    match findStruct m.structs id with
    | none => tyR "TypeError: struct id not found in module"
    | some d =>
      if lanes.length != d.fields.length then tyR "TypeError: struct lane arity"
      else match nth? d.fields field with
      | none => ubR "field is out of bounds"
      | some declared => do
        expectTy m.pointerBits v declared
        pure (.struct id (setNth lanes field v))
  | _ => tyR "TypeError: insert_field requires an aggregate"

def isScalarTy : Ty → Bool
  | .int _ | .bool | .ptr => true
  | _ => false

/-- Scalar poison agrees with the reference interpreter's scalar_poison.
    In particular Undef Struct is UB, NOT a fresh/default aggregate. -/
def undefVal (ty : Ty) : R Val :=
  if isScalarTy ty then pure (.poison ty)
  else ubR "undef of non-scalar type is not executable (aggregate poison unmodelled)"

/-- No pointer images or binding-frame handles enter abstract cell storage. -/
def isCellTy : Ty → Bool
  | .int _ | .bool => true
  | _ => false

def findCell : List Cell → Nat → Option Cell
  | [], _ => none
  | c :: cs, id => if c.id == id then some c else findCell cs id

def putCell : List Cell → Cell → List Cell
  | [], _ => []
  | c :: cs, value => if c.id == value.id then value :: cs else c :: putCell cs value

def cellAddress (k : Core) (ptr : Val) (ty : Ty) : R Cell :=
  match ptr with
  | .cellPtr id =>
    match findCell k.cells id with
    | none => ubR "private cell address has no allocation"
    | some c =>
      if !c.ty.beq ty then tyR "TypeError: private cell access type mismatch"
      else if !isCellTy ty then unsupR "private_cell.type"
      else pure c
  | _ => tyR "TypeError: expected a private cell address"

def expectCell (k : Core) (ptr : Val) (ty : Ty) : R Cell := do
  rejectPoison ptr "private cell address"
  cellAddress k ptr ty

def memNat : List Nat → Nat → Bool
  | [], _ => false
  | a :: as, x => a == x || memNat as x

def removeNat : List Nat → Nat → List Nat
  | [], _ => []
  | a :: as, x => if a == x then as else a :: removeNat as x

def expectFrame (v : Val) : R (Nat × List (Option Val)) :=
  match v with
  | .frame l s => .ok (l, s)
  | _ => tyR "TypeError: expected a binding-frame handle"

/-- The frame-open guard of `BindSlot`/`LoadSlot`: `c` runs only while
    lineage `l` is open. -/
def openedAt (k : Core) (l : Nat) (what : String) (c : R Core) : R Core :=
  if memNat k.openFrames l then c else ubR s!"{what}: frame is not open"

/-- Bind the node's declared results to the produced values (`bind_results`). -/
def bindResults (k : Core) (node : Node) (vs : List Val) : R Core :=
  if node.results.length != vs.length then
    tyR "MalformedInstruction: instruction result arity mismatch"
  else
    .ok { k with env := (node.results.zip vs).reverse ++ k.env }

/-! ## The tensor contraction (`Inst::TensorContract`, wire v67)

A tensor value carries its extents and its residues in row-major order. The
contraction is XLA's DotGeneral over integers. Its static rules (the element
types agree, every paired axis is in range, no axis is paired twice, the
result rank is the batch axes plus both operands' free axes) and each
operand's well-formedness (each extent below `2^pointerBits`, as many residues
as the extents' product, each in range at the element's width) are type
errors. Paired extents that differ, and a result of `2^pointerBits` elements
or more, are undefined behaviour, by the reference interpreter's reasons.
Each result element is the wrapping sum, a left fold from `0` over the
contracted multi-indices in row-major order, of the wrapping products
(`intBin`'s `.mul` and `.add` residues). -/

/-- The row-major offset of a multi-index: `Σ idx[i] · Π dims[i+1..]`. -/
def offsetIn : List Nat → List Nat → Nat
  | _ :: ds, i :: is => i * prodL ds + offsetIn ds is
  | _, _ => 0

/-- `[0, 1, …, n - 1]`. -/
def upTo : Nat → List Nat
  | 0 => []
  | n + 1 => upTo n ++ [n]

/-- A shape's multi-indices in row-major order (the last axis fastest). -/
def multiIdx : List Nat → List (List Nat)
  | [] => [[]]
  | d :: ds => (upTo d).flatMap (fun i => (multiIdx ds).map (fun t => i :: t))

/-- The position of axis `x` in `xs`. -/
def axisPos : List Nat → Nat → Option Nat
  | [], _ => none
  | a :: as, x => if a == x then some 0 else (axisPos as x).map (· + 1)

/-- No element repeats. -/
def distinctNat : List Nat → Bool
  | [] => true
  | a :: as => !memNat as a && distinctNat as

/-- The axes of `0..n` that no pair names, ascending. -/
def freeAxes (n : Nat) (paired : List Nat) : List Nat :=
  (upTo n).filter (fun ax => !memNat paired ax)

/-- The coordinate an operand reads along its axis `ax` at result
    multi-index `o` and contracted multi-index `c`: a batch axis reads `o`'s
    batch coordinate, a free axis `o`'s free coordinate (those start at
    `base`), a contracted axis `c`'s coordinate. -/
def axisAt (bat con free : List Nat) (base : Nat) (o c : List Nat) (ax : Nat) : Nat :=
  match axisPos bat ax with
  | some i => getN o i
  | none =>
    match axisPos free ax with
    | some t => getN o (base + t)
    | none =>
      match axisPos con ax with
      | some j => getN c j
      | none => 0

/-- One accumulation step at width `w`: `acc + x * y`, the product and the sum
    each wrapping (`intBin .mul`, then `intBin .add`). -/
def macR (w acc x y : Nat) : Nat := (acc + (x * y) % modulus w) % modulus w

/-- The result's extents: the batch extents, then the left operand's free
    extents, then the right operand's. -/
def contractDims (batch contract : List (Nat × Nat)) (da db : List Nat) : List Nat :=
  (batch.map Prod.fst).map (getN da) ++
    (freeAxes da.length (batch.map Prod.fst ++ contract.map Prod.fst)).map (getN da) ++
    (freeAxes db.length (batch.map Prod.snd ++ contract.map Prod.snd)).map (getN db)

/-- The result's residues, row-major over its multi-indices. -/
def contractElems (w : Nat) (batch contract : List (Nat × Nat)) (da db xa xb : List Nat) :
    List Nat :=
  let lb := batch.map Prod.fst
  let rb := batch.map Prod.snd
  let lc := contract.map Prod.fst
  let rc := contract.map Prod.snd
  let lf := freeAxes da.length (lb ++ lc)
  let rf := freeAxes db.length (rb ++ rc)
  (multiIdx (contractDims batch contract da db)).map (fun o =>
    (multiIdx (lc.map (getN da))).foldl (fun acc c =>
      macR w acc
        (getN xa (offsetIn da ((upTo da.length).map (axisAt lb lc lf lb.length o c))))
        (getN xb (offsetIn db ((upTo db.length).map (axisAt rb rc rf (lb.length + lf.length) o c)))))
      0)

/-- Static rules 2 and 3: every paired axis is in range, and no axis of
    either operand is paired twice. -/
def contractAxesOk (batch contract : List (Nat × Nat)) (p q : Nat) : Bool :=
  (batch ++ contract).all (fun pr => decide (pr.1 < p) && decide (pr.2 < q)) &&
    distinctNat ((batch ++ contract).map Prod.fst) &&
    distinctNat ((batch ++ contract).map Prod.snd)

/-- An operand's well-formedness: each extent below `2^pointerBits`, as many
    residues as the extents' product, each a residue at the element's width. -/
def tensorWF (pointerBits : Nat) (e : IntTy) (dims elems : List Nat) : Bool :=
  dims.all (fun d => decide (d < modulus pointerBits)) && prodL dims == elems.length &&
    elems.all (fun x => decide (x < modulus (e.bits pointerBits)))

/-- `eval_tensor_contract`: the checks in the interpreter's order, then the
    elements. -/
def evalContract (pointerBits : Nat) (ty : Ty) (batch contract : List (Nat × Nat))
    (a b : Val) : R Val := do
  rejectPoison a "tensor_contract"
  rejectPoison b "tensor_contract"
  match ty, a, b with
  | .tensor e r, .tensor ea da xa, .tensor eb db xb =>
    if !(ea.code == e.code && eb.code == e.code) then
      tyR "TypeError: tensor contraction: an operand's element type is not the result's"
    else if !contractAxesOk batch contract da.length db.length then
      tyR "TypeError: tensor contraction: an axis pair is out of range or names an axis twice"
    else if r != batch.length + (da.length - batch.length - contract.length) +
        (db.length - batch.length - contract.length) then
      tyR "TypeError: tensor contraction: the result rank is not the batch and free axes"
    else if !tensorWF pointerBits e da xa then
      tyR "TypeError: tensor contraction: the left operand is not a well-formed tensor"
    else if !tensorWF pointerBits e db xb then
      tyR "TypeError: tensor contraction: the right operand is not a well-formed tensor"
    else if !(batch ++ contract).all (fun pr => getN da pr.1 == getN db pr.2) then
      ubR "tensor contraction: paired axes have different extents"
    else if modulus pointerBits ≤ prodL (contractDims batch contract da db) then
      ubR "tensor contraction: the result has more elements than usize holds"
    else
      pure (.tensor e (contractDims batch contract da db)
        (contractElems (e.bits pointerBits) batch contract da db xa xb))
  | _, _, _ => tyR "TypeError: tensor contraction: its operands and result must be tensors"

/-- The signature check of a call boundary (`check_signature_values`). -/
def checkSig (pointerBits : Nat) : List Val → List Ty → R Unit
  | [], [] => .ok ()
  | v :: vs, t :: ts => do
    rejectPoison v "signature boundary"
    if v.ty.beq t then do
      expectTy pointerBits v t
      checkSig pointerBits vs ts
    else tyR "SignatureMismatch: type mismatch"
  | _, _ => tyR "SignatureMismatch: arity mismatch"

def findBlock : List Block → Nat → Option Block
  | [], _ => none
  | b :: bs, id => if b.id == id then some b else findBlock bs id

/-- `bind_block_params`. -/
def bindParams (pointerBits : Nat) (env : List (Nat × Val)) :
    List (Nat × Ty) → List Val → R (List (Nat × Val))
  | [], [] => .ok env
  | (x, t) :: ps, v :: vs => do
    expectTy pointerBits v t
    bindParams pointerBits ((x, v) :: env) ps vs
  | _, _ => tyR "MalformedInstruction: block parameter arity mismatch"

/-- Enter block `target` of the current function with `args`. -/
def jump (pointerBits : Nat) (k : Core) (target : Nat) (args : List Val) : R Core :=
  match findBlock k.fn.blocks target with
  | none => tyR "MissingBlock: block not found"
  | some b => do
    let env ← bindParams pointerBits k.env b.params args
    pure { k with block := b, pc := 0, env := env }

/-- What one step did: continue in a new state, or finish with a verdict. -/
inductive StepR where
  | cont (k : Core)
  | done (o : Out)

def ofR (x : R Core) : StepR :=
  match x with
  | .ok k => .cont k
  | .stop o => .done o

def next (k : Core) : Core := { k with pc := k.pc + 1 }

/-- The decimal spelling of a natural number. -/
def decStr (n : Nat) : String := toString n

/-- Rust's `{:#x}`. -/
def hexStr (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def assertOperand (k : Core) (x : Nat) : R Nat := do
  let v ← getV k x
  rejectPoison v "assert"
  match v with
  | .int _ a => pure a
  | _ => tyR "TypeError: assert operand requires an integer"

/-- `AssertKind::panic_message`, `core`'s text. -/
def assertMessage (k : Core) : AssertKind → R String
  | .unspecified => pure "assertion failed"
  | .overflow op => pure (match op with
    | 0 => "attempt to add with overflow"
    | 1 => "attempt to subtract with overflow"
    | 2 => "attempt to multiply with overflow"
    | 3 => "attempt to divide with overflow"
    | 4 => "attempt to calculate the remainder with overflow"
    | 5 => "attempt to shift left with overflow"
    | 6 => "attempt to shift right with overflow"
    | _ => "attempt to negate with overflow")
  | .divByZero => pure "attempt to divide by zero"
  | .remByZero => pure "attempt to calculate the remainder with a divisor of zero"
  | .nullPtr => pure "null pointer dereference occurred"
  | .bounds index len => do
    let i ← assertOperand k index
    let l ← assertOperand k len
    pure s!"index out of bounds: the len is {decStr l} but the index is {decStr i}"
  | .misaligned required found => do
    let r ← assertOperand k required
    let f ← assertOperand k found
    pure s!"misaligned pointer dereference: address must be a multiple of {hexStr r} but is {hexStr f}"

/-- An integer or `Bool` operand as the interpreter resizes it
    (`expect_integer_resize_value`): its width, signedness and raw bits. -/
def resizeOf (pointerBits : Nat) (v : Val) : R (Nat × Bool × Nat) :=
  match v with
  | .int t a => .ok (t.bits pointerBits, t.signed, a)
  | .bool b => .ok (1, false, b2n b)
  | _ => tyR "TypeError: expected integer or bool value"

/-- `eval_bitcast` at one type: the value itself (integers, `Bool`s and
    pointers, the types with a bit width the fragment carries). -/
def bitcastSame : Ty → Val → R Val
  | .int _, v => .ok v
  | .bool, v => .ok v
  | .ptr, v => .ok v
  | _, _ => unsupR "cast.bitcast"

/-- `eval_bitcast` between two integer types of one width: the residue. -/
def bitcastInt (pointerBits : Nat) : Ty → Ty → Val → R Val
  | .int s, .int t, .int _ a =>
    if s.bits pointerBits == t.bits pointerBits then .ok (.int t (a % modulus (t.bits pointerBits)))
    else tyR "TypeError: Bitcast: bit width mismatch"
  | _, _, _ => unsupR "cast.bitcast"

/-- `eval_cast` for the integer casts, once the operand passed
    `reject_partial` and `expect_ty`. -/
def castCore (pointerBits : Nat) (op : CastOp) (src dst : Ty) (v : Val) : R Val :=
  match op with
  | .trunc => do
    let (_, _, a) ← resizeOf pointerBits v
    match dst with
    | .bool => pure (.bool (a % 2 == 1))
    | .int t => pure (.int t (a % modulus (t.bits pointerBits)))
    | _ => tyR "TypeError: Trunc: destination is not integer"
  | .zext => do
    let (_, _, a) ← resizeOf pointerBits v
    match dst with
    | .int t => pure (.int t (a % modulus (t.bits pointerBits)))
    | _ => tyR "TypeError: ZExt: destination is not integer"
  | .sext => do
    let (w, _, a) ← resizeOf pointerBits v
    match dst with
    | .int t => pure (.int t (resid (t.bits pointerBits) (readInt true w a)))
    | _ => tyR "TypeError: SExt: destination is not integer"
  | .bitcast => if src.beq dst then bitcastSame src v else bitcastInt pointerBits src dst v

/-- `eval_cast` for the integer casts. -/
def evalCast (pointerBits : Nat) (op : CastOp) (src dst : Ty) (v : Val) : R Val := do
  rejectPoison v "cast"
  expectTy pointerBits v src
  castCore pointerBits op src dst v

/-- `Val` equality, as the interpreter's derived `PartialEq` compares a
    `Switch` case's value with the scrutinee (integers and `Bool`s only). -/
def valEqScalar : Val → Val → Bool
  | .int s a, .int t b => s.code == t.code && a == b
  | .bool a, .bool b => a == b
  | _, _ => false

/-- The first case whose constant equals the scrutinee, else the default. -/
def switchTarget (m : Module) (v : Val) :
    List (Const × Nat × List Nat) → R (Option (Nat × List Nat))
  | [] => .ok none
  | (c, t, as) :: rest => do
    let cv ← constVal m 8 v.ty c
    if valEqScalar cv v then pure (some (t, as)) else switchTarget m v rest

/-! ### Memory: the value level

What a memory instruction computes from values alone (shared by the
executable and the relation, like the operators): layouts, alignments, the
pointer an operand must be, a store's byte image and a load's value, the
count of an `Alloca` and the offset of a `GEP`. Every check that reads or
moves the memory itself (liveness, bounds, alignment of an address,
allocation, deallocation) is a piece of the step below, which the relation
states with its own rules (`Accesses`, `Reads`, `Allocates`, `Frees`,
`Offsets`). The model is MiniRust's (`mem/basic.md`): an allocation is a list
of abstract bytes at an address, a pointer is an allocation id and an offset,
an integer is its little-endian bytes (`Endianness::encode`), and a byte that
was never written is `Uninit`; SemR follows the reference interpreter where
the two differ (see `accessAt`). -/

/-- The interpreter's u64 arithmetic bound, including counts and offsets on
    32-bit targets. Target addresses have the additional bound `2^pointerBits`. -/
def addrSpace : Nat := 2 ^ 64

/-- Exact storage geometry, with checked u64 bit sizes and target address width.
    This predicate grants neither initialized bytes nor access permission. -/
def storageGeometry (pointerBits size align : Nat) : Bool :=
  align != 0 && Nat.land align (align - 1) == 0 && size % align == 0 &&
  size * 8 < 2^64 && align * 8 < 2^64 &&
  (if pointerBits == 32 then size < 2^32 && align ≤ 2^31
   else pointerBits == 64)

/-- `byte_size` and `byte_align` of a type an allocation or a `GEP` steps over:
    integers, `Bool`, target-sized pointers and `()`. -/
def layoutOf (pointerBits : Nat) : Ty → R (Nat × Nat)
  | .int t => .ok (t.bytes pointerBits, t.bytes pointerBits)
  | .bool => .ok (1, 1)
  | .ptr => .ok (pointerBits / 8, pointerBits / 8)
  | .unit => .ok (0, 1)
  | .storage size align =>
    if storageGeometry pointerBits size align then .ok (size, align)
    else tyR "TypeError: invalid storage geometry"
  | _ => unsupR "mem.layout"

/-- The size (and alignment) of a type a `Load` or `Store` accesses: the
    integers and `Bool`. A pointer's bytes carry provenance, and this slice
    keeps none in memory, so a pointer-typed access is refused by name. -/
def scalarLayout (pointerBits : Nat) : Ty → R Nat
  | .int t => .ok (t.bytes pointerBits)
  | .bool => .ok 1
  | _ => unsupR "mem.access.ty"

/-- A non-zero power of two (`u64::is_power_of_two`). -/
def isPow2 (a : Nat) : Bool := a != 0 && Nat.land a (a - 1) == 0

/-- `checked_align`. -/
def checkAlign (a : Nat) : R Nat :=
  if isPow2 a then .ok a
  else tyR s!"TypeError: alignment {decStr a} must be a non-zero power of two"

/-- `expect_pointer`: a pointer with provenance; poison and the null pointer
    are undefined behaviour to reach through, anything else a type error. -/
def expectPtr (v : Val) (what : String) : R (Nat × Nat) := do
  rejectPoison v what
  match v with
  | .ptr a o => pure (a, o)
  | .nullPtr => ubR s!"{what}: null pointer dereference"
  | _ => tyR s!"TypeError: {what}: expected pointer value"

/-- Byte `i` of an allocation's data: past the written prefix, uninitialized. -/
def byteAt (d : List AByte) (i : Nat) : AByte :=
  match nth? d i with
  | some b => b
  | none => .uninit

/-- The `n` bytes at offset `o`. -/
def readBytes (d : List AByte) : Nat → Nat → List AByte
  | _, 0 => []
  | o, n + 1 => byteAt d o :: readBytes d (o + 1) n

/-- Byte `i` set to `b`, the prefix padded with uninitialized bytes. -/
def setByte : List AByte → Nat → AByte → List AByte
  | [], 0, b => [b]
  | [], n + 1, b => .uninit :: setByte [] n b
  | _ :: xs, 0, b => b :: xs
  | x :: xs, n + 1, b => x :: setByte xs n b

/-- The bytes `bs` written at offset `o`. -/
def writeBytes : List AByte → Nat → List AByte → List AByte
  | d, _, [] => d
  | d, o, b :: bs => writeBytes (setByte d o b) (o + 1) bs

/-- `n` uninitialized bytes. -/
def uninitBytes : Nat → List AByte
  | 0 => []
  | n + 1 => .uninit :: uninitBytes n

/-- The `n`-byte little-endian image of `x` (`Endianness::encode`, little). -/
def leBytes : Nat → Nat → List AByte
  | 0, _ => []
  | n + 1, x => .init (x % 256) :: leBytes n (x / 256)

/-- The number a little-endian image of initialized bytes spells. -/
def fromLE : List AByte → Nat
  | [] => 0
  | .init b :: bs => b + 256 * fromLE bs
  | .uninit :: bs => 256 * fromLE bs

/-- The position of the first uninitialized byte. -/
def firstUninit : List AByte → Option Nat
  | [] => none
  | .uninit :: _ => some 0
  | .init _ :: bs => (firstUninit bs).map (· + 1)

/-- A stored value's bytes (`encode_image`): an integer its little-endian
    residue, a `Bool` one byte `0` or `1`. -/
def encodeVal (pointerBits : Nat) (v : Val) : R (List AByte) :=
  match v with
  | .int t a => .ok (leBytes (t.bytes pointerBits) a)
  | .bool b => .ok [.init (b2n b)]
  | _ => unsupR "mem.access.ty"

/-- A loaded value from its initialized bytes (`decode_leaf`). A `Bool` byte
    other than `0`/`1` is refused by name: the interpreter reads any non-zero
    byte as `true`, MiniRust's `Bool` decode calls it undefined behaviour, and
    SemR takes neither side. -/
def decodeVal (ty : Ty) (bs : List AByte) : R Val :=
  match ty with
  | .int t => .ok (.int t (fromLE bs))
  | .bool =>
    match bs with
    | [.init 0] => .ok (.bool false)
    | [.init 1] => .ok (.bool true)
    | _ => unsupR "mem.bool_byte"
  | _ => unsupR "mem.access.ty"

/-- The byte image a `Store` at type `ty` (of `size` bytes) writes for `v`:
    poison writes its bytes as they are (uninitialized), and only a plain
    store may move it (`eval_store`'s copy-propagates-poison arm); any other
    value has type `ty` and is encoded. -/
def storeImage (pointerBits : Nat) (ty : Ty) (vol : Bool) (size : Nat) (v : Val) : R (List AByte) :=
  match v with
  | .poison _ =>
    if vol then ubR "Store (atomic/volatile): use of an uninitialized value (poison)"
    else do expectTy pointerBits v ty; pure (uninitBytes size)
  | .partialBytes _ bs =>
    if vol then ubR "Store (atomic/volatile): use of an uninitialized value (poison)"
    else do
      expectTy pointerBits v ty
      if bs.length == size then pure bs
      else tyR "TypeError: Store: poison image size does not match type size"
  | _ => do expectTy pointerBits v ty; encodeVal pointerBits v

/-- The count operand of an `Alloca`, if it has one. -/
def getCount (k : Core) : Option Nat → R (Option Val)
  | none => .ok none
  | some c => do let v ← getV k c; pure (some v)

/-- An `Alloca`'s size: its element size times its count (`1` without one);
    the count is a positive integer that fits `u64`, and the size fits too. -/
def allocSize (pointerBits esize : Nat) : Option Val → R Nat
  | none => if addrSpace ≤ esize then ubR "Alloca: allocation size overflow" else .ok esize
  | some v => do
    let (t, a) ← expectInt v
    if a == 0 || (t.signed && isNeg (t.bits pointerBits) a) then ubR "Alloca: count must be positive"
    else if addrSpace ≤ a then ubR s!"Alloca: count {decStr a} does not fit u64"
    else if addrSpace ≤ esize * a then ubR "Alloca: allocation size overflow"
    else pure (esize * a)

/-- A `GEP`'s byte offset, accumulated over its indices from `d`: each index a
    non-negative integer that fits `u64`, scaled by the element size, the
    products and the sum below `2^64`. -/
def gepDelta (pointerBits esize : Nat) : List Val → Nat → R Nat
  | [], d => .ok d
  | v :: vs, d => do
    let (t, a) ← expectInt v
    if t.signed && isNeg (t.bits pointerBits) a then ubR s!"GEP: negative index -{decStr (mag (t.bits pointerBits) a)}"
    else if addrSpace ≤ a then ubR s!"GEP: index {decStr a} does not fit u64"
    else if addrSpace ≤ esize * a then ubR "GEP: byte offset overflow"
    else if addrSpace ≤ d + esize * a then ubR "GEP: pointer offset overflow"
    else gepDelta pointerBits esize vs (d + esize * a)

/-- `x` rounded up to a multiple of the power of two `a` (`align_addr`). -/
def alignUp (x a : Nat) : Nat := (x + (a - 1)) - (x + (a - 1)) % a

/-! ### The pieces of a step

Each piece is the part of one instruction's step that follows its operand
reads: the executable `execNode` below is these pieces in sequence, and the
relation `Step` states each piece as an inductive relation of its own. -/

/-- A value read as a `Bool` condition: `some b` for `.bool b`, else `none`. -/
def asBool : Val → Option Bool
  | .bool b => some b
  | _ => none

/-- `Select` on its evaluated condition. -/
def selectOn (k : Core) (node : Node) (tv ev cv : Val) : R Core :=
  match asBool cv with
  | some true => bindResults (next k) node [tv]
  | some false => bindResults (next k) node [ev]
  | none => tyR "TypeError: select requires a bool condition"

/-- `BindSlot` of `v` into slot `slot` of the open frame `(l, s)`. -/
def bindSlotAt (k : Core) (node : Node) (l : Nat) (s : List (Option Val)) (slot : Nat) (v : Val) :
    R Core :=
  if s.length ≤ slot then ubR "BindSlot: slot out of range"
  else bindResults (next k) node [.frame l (setNth s slot (some v))]

/-- `LoadSlot` at type `ty` from slot contents `s`. -/
def loadSlotAt (pointerBits : Nat) (k : Core) (node : Node) (slot : Nat) (ty : Ty) (s : List (Option Val)) : R Core :=
  match nth? s slot with
  | none => ubR "LoadSlot: slot out of range"
  | some (some v) => do expectTy pointerBits v ty; bindResults (next k) node [v]
  | some none =>
    if isScalarTy ty then bindResults (next k) node [.poison ty]
    else ubR "LoadSlot: poison of a non-scalar type"

/-- `CloseFrame` of lineage `l`. -/
def closeAt (k : Core) (node : Node) (l : Nat) : R Core :=
  if memNat k.openFrames l then
    bindResults { next k with openFrames := removeNat k.openFrames l } node []
  else ubR "CloseFrame: frame is not open (double close)"

/-- `Assert` on its evaluated condition. -/
def assertOn (k : Core) (kind : AssertKind) (cv : Val) : R Core :=
  match asBool cv with
  | some true => pure (next k)
  | some false => do
    let msg ← assertMessage k kind
    .stop (.panic msg)
  | none => tyR "TypeError: assert requires bool"

/-- The caller record a call suspends. -/
def suspend (k : Core) (node : Node) : Caller :=
  { fn := k.fn, sig := k.sig, block := k.block, pc := k.pc, env := k.env, depth := k.depth,
    node := node }

/-- Entering callee `f` (signature `sig`, arguments `vs` checked). -/
def enterFn (pointerBits : Nat) (k : Core) (node : Node) (f : Func) (sig : FuncTy) (vs : List Val) : R Core :=
  if f.blocks.isEmpty then unsupR "interprocedural_call" else
  match findBlock f.blocks f.entry with
  | none => tyR "MissingBlock: entry block not found"
  | some b => do
    let env ← bindParams pointerBits [] b.params vs
    pure { k with fn := f, sig := sig, block := b, pc := 0, env := env,
                  depth := k.depth - 1, stack := suspend k node :: k.stack }

/-- A call whose callee `f` has signature `sig`: a variadic signature is
    refused (by name for a declaration), else the arguments are checked and
    the callee entered. -/
def callSigned (pointerBits : Nat) (k : Core) (node : Node) (f : Func) (sig : FuncTy) (vs : List Val) : R Core :=
  if sig.vararg then
    (if f.blocks.isEmpty then unsupR "call.vararg"
     else tyR "SignatureMismatch: variadic definition")
  else do
    checkSig pointerBits vs sig.params
    enterFn pointerBits k node f sig vs

/-- A call of `f`, by its signature slot. -/
def callSig (pointerBits : Nat) (k : Core) (node : Node) (f : Func) (vs : List Val) : Option FuncTy → R Core
  | none => tyR "SignatureMismatch: undefined signature"
  | some sig => callSigned pointerBits k node f sig vs

/-- A call, by the function the callee id names. -/
def callFn (m : Module) (k : Core) (node : Node) (vs : List Val) : Option Func → R Core
  | none => tyR "MissingFunction: undefined function"
  | some f => callSig m.pointerBits k node f vs (nth? m.funcTys f.ty)

/-- A direct call of `callee` on the evaluated arguments `vs`. -/
def callOn (m : Module) (k : Core) (node : Node) (callee : Nat) (vs : List Val) : R Core :=
  if k.depth == 0 then .stop .outOfFuel
  else callFn m k node vs (m.functions.find? (fun f => f.id == callee))

/-- `CondBr` on its evaluated condition. -/
def branchOn (pointerBits : Nat) (k : Core) (tT : Nat) (tA : List Nat) (eT : Nat) (eA : List Nat) (cv : Val) : R Core :=
  match asBool cv with
  | some true => do let vs ← getVs k tA; jump pointerBits k tT vs
  | some false => do let vs ← getVs k eA; jump pointerBits k eT vs
  | none => tyR "TypeError: cond_br requires bool"

/-- `Return` of the checked values `vs`: the run ends with them from the
    outermost call (`.stop (.ret vs)`), else the caller resumes. -/
def returnTo (k : Core) (vs : List Val) : R Core :=
  match k.stack with
  | [] => .stop (.ret vs)
  | c :: rest =>
    bindResults { k with fn := c.fn, sig := c.sig, block := c.block, pc := c.pc + 1,
                         env := c.env, depth := c.depth, stack := rest } c.node vs

/-- The checks of an access of `size` bytes at offset `o` of allocation `al`
    with alignment `align` (`MemoryState::checked_access`), in the
    interpreter's order: live (else use after `Dealloc`, MiniRust's
    "dereferencing pointer to dead allocation"), an address that fits, the
    address aligned, the end of the range that fits, the range in bounds.
    MiniRust's `load`/`store` check the alignment before the liveness; on a
    dead, misaligned pointer the two name different undefined behaviour, and
    SemR names the interpreter's. The fourth check (`access range overflow`,
    the interpreter's `checked_add` of the offset and the size) is kept for
    the interpreter's order but never fails after the second: every slot's
    address is at least 1024 and an access is at most 16 bytes, so an offset
    whose end passes `2^64` gives an address past it first. -/
def accessAlloc (op : String) (al : Alloc) (o size align : Nat) : R Alloc :=
  if al.live then
    if decide (addrSpace ≤ al.base + o) then ubR s!"{op}: pointer address overflow"
    else if (al.base + o) % align != 0 then
      ubR s!"{op}: pointer address {decStr (al.base + o)} is not aligned to {decStr align}"
    else if decide (addrSpace ≤ o + size) then ubR s!"{op}: access range overflow"
    else if decide (al.size < o + size) then
      ubR s!"{op}: access [{decStr o}..{decStr (o + size)}) is out of bounds for allocation size {decStr al.size}"
    else .ok al
  else ubR s!"{op}: use after dealloc"

/-- An access through the pointer `(a, o)`. -/
def accessAt (m : Mem) (op : String) (a o size align : Nat) : R Alloc :=
  match nth? m.allocs a with
  | none => ubR s!"{op}: unknown allocation {decStr a}"
  | some al => accessAlloc op al o size align

/-- A `Load` of `ty` that read the bytes `bs` at offset `o`: initialized bytes
    are decoded; a plain load of partly uninitialized bytes reads them as
    poison (`PartialBytes`), a volatile one is undefined behaviour at the
    first uninitialized byte. -/
def readOut (k : Core) (node : Node) (ty : Ty) (vol : Bool) (o : Nat) (bs : List AByte) : R Core :=
  match firstUninit bs with
  | none => do let v ← decodeVal ty bs; bindResults (next k) node [v]
  | some i =>
    if vol then ubR s!"Load: reading uninitialized byte at offset {decStr (o + i)}"
    else bindResults (next k) node [.partialBytes ty bs]

/-- The memory after the bytes `bs` are written at offset `o` of allocation
    `a` (whose record is `al`). -/
def written (m : Mem) (a o : Nat) (al : Alloc) (bs : List AByte) : Mem :=
  { m with allocs := setNth m.allocs a { al with data := writeBytes al.data o bs } }

/-- A fresh allocation of `size` bytes aligned to `align` (`alloc_with_slack`,
    no slack: a stack slot's bounds are exact): placed at the next free
    address rounded up to `align`, the bump moving past it by its size (by
    one for a zero-sized slot). The u64 exclusive end must not overflow;
    the last byte must also be target-addressable. Thus an exclusive end of
    `2^32` fits wasm32, whereas `2^64` overflows u64 even on a 64-bit target. -/
def allocAt (pointerBits : Nat) (k : Core) (node : Node) (size align : Nat) : R Core :=
  if decide (addrSpace ≤ k.mem.nextAddr + (align - 1)) then .stop .outOfMemory
  else if decide (addrSpace ≤ alignUp k.mem.nextAddr align + max size 1) then .stop .outOfMemory
  else if decide (2 ^ pointerBits < alignUp k.mem.nextAddr align + max size 1) then .stop .outOfMemory
  else
    bindResults
      { next k with
        mem := { allocs := k.mem.allocs ++
                   [{ base := alignUp k.mem.nextAddr align, size := size, align := align,
                      live := true, data := [] }],
                 nextAddr := alignUp k.mem.nextAddr align + max size 1 } }
      node [.ptr k.mem.allocs.length 0]

/-- `Dealloc` through the pointer `(a, o)`: only the base of a live
    allocation, once (`MemoryState::dealloc`; MiniRust's `deallocate`, which
    also refuses an interior pointer and a dead allocation). -/
def freeAlloc (k : Core) (node : Node) (a : Nat) (al : Alloc) : R Core :=
  if al.live then
    bindResults { next k with mem := { k.mem with allocs := setNth k.mem.allocs a { al with live := false } } }
      node []
  else ubR "Dealloc: allocation is already dead"

def freeAt (k : Core) (node : Node) (a o : Nat) : R Core :=
  match o != 0 with
  | true => ubR "Dealloc: pointer must reference allocation base"
  | false =>
    match nth? k.mem.allocs a with
    | none => ubR s!"Dealloc: unknown allocation {decStr a}"
    | some al => freeAlloc k node a al

/-- The pointer a `GEP` makes: the base's allocation, its offset moved by
    `d`; the offset must fit `u64` (pointer arithmetic: no liveness or bounds
    check, as the interpreter, which ignores `inbounds`; narrow targets also
    check the original and resulting absolute addresses without inspecting
    allocation liveness. MiniRust's in-bounds
    offset past the slot or from a dead slot is undefined behaviour). -/
def gepAt (pointerBits : Nat) (k : Core) (node : Node) (a o d : Nat) : R Core :=
  if decide (addrSpace ≤ o + d) then ubR "GEP: pointer offset overflow"
  else
    if pointerBits != 64 then
      match nth? k.mem.allocs a with
        | none => ubR s!"GEP: unknown allocation {decStr a}"
        | some al =>
          if decide (addrSpace ≤ al.base + o) || decide (2 ^ pointerBits ≤ al.base + o) then
            ubR "GEP: pointer address overflow"
          else if decide (addrSpace ≤ al.base + o + d) then ubR "GEP: pointer offset overflow"
          else if decide (2 ^ pointerBits ≤ al.base + o + d) then
            ubR s!"GEP: address {hexStr (al.base + o + d)} is outside the target's address space (highest address {hexStr (2 ^ pointerBits - 1)})"
          else bindResults (next k) node [.ptr a (o + d)]
    else bindResults (next k) node [.ptr a (o + d)]

/-- `binop` after the node at `pc` is read. -/
def binopStep (pointerBits : Nat) (k : Core) (node : Node) (op : BinOp) (ty : Ty) (l r : Nat) : R Core := do
  let a ← getV k l
  let b ← getV k r
  let v ← evalBinop pointerBits op ty a b
  bindResults (next k) node [v]

/-- `unop` after the node at `pc` is read. -/
def unopStep (pointerBits : Nat) (k : Core) (node : Node) (op : UnOp) (ty : Ty) (x : Nat) : R Core := do
  let a ← getV k x
  let v ← evalUnop pointerBits op ty a
  bindResults (next k) node [v]

/-- `overflow` after the node at `pc` is read. -/
def overflowStep (pointerBits : Nat) (k : Core) (node : Node) (op : OvfOp) (ty : Ty) (l r : Nat) : R Core := do
  let a ← getV k l
  let b ← getV k r
  let vs ← evalOverflow pointerBits op ty a b
  bindResults (next k) node vs

/-- `icmp` after the node at `pc` is read. -/
def icmpStep (pointerBits : Nat) (k : Core) (node : Node) (op : ICmpOp) (ty : Ty) (l r : Nat) : R Core := do
  let a ← getV k l
  let b ← getV k r
  let v ← evalIcmp pointerBits op ty a b
  bindResults (next k) node [v]

/-- `tensorContract` after the node at `pc` is read. -/
def tensorContractStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (l r : Nat)
    (batch contract : List (Nat × Nat)) : R Core := do
  let a ← getV k l
  let b ← getV k r
  let v ← evalContract pointerBits ty batch contract a b
  bindResults (next k) node [v]

/-- `const` after the node at `pc` is read. -/
def constStep (m : Module) (k : Core) (node : Node) (ty : Ty) (c : Const) : R Core := do
  let v ← constVal m 8 ty c
  bindResults (next k) node [v]

/-- `copy` after the node at `pc` is read. -/
def copyStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (x : Nat) : R Core := do
  let a ← getV k x
  expectTy pointerBits a ty
  bindResults (next k) node [a]

/-- `select` after the node at `pc` is read. -/
def selectStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (c t e : Nat) : R Core := do
  let cv ← getV k c
  let tv ← getV k t
  let ev ← getV k e
  rejectPoison cv "select"
  expectTy pointerBits tv ty
  expectTy pointerBits ev ty
  selectOn k node tv ev cv

/-- `extractField` after the node at `pc` is read. -/
def extractFieldStep (m : Module) (k : Core) (node : Node) (ty : Ty) (agg field : Nat) : R Core := do
  let a ← getV k agg
  let v ← evalExtract m ty a field
  bindResults (next k) node [v]

/-- `insertField` after the node at `pc` is read. -/
def insertFieldStep (m : Module) (k : Core) (node : Node) (ty : Ty) (agg field x : Nat) : R Core := do
  let a ← getV k agg
  let v ← getV k x
  let w ← evalInsert m ty a field v
  bindResults (next k) node [w]

/-- `bindSlot` after the node at `pc` is read. -/
def bindSlotStep (k : Core) (node : Node) (f slot x : Nat) : R Core := do
  let h ← getV k f
  let ls ← expectFrame h
  openedAt k ls.1 "BindSlot" (do
    let v ← getV k x
    bindSlotAt k node ls.1 ls.2 slot v)

/-- `loadSlot` after the node at `pc` is read. -/
def loadSlotStep (pointerBits : Nat) (k : Core) (node : Node) (f slot : Nat) (ty : Ty) : R Core := do
  let h ← getV k f
  let ls ← expectFrame h
  openedAt k ls.1 "LoadSlot" (loadSlotAt pointerBits k node slot ty ls.2)

/-- `closeFrame` after the node at `pc` is read. -/
def closeFrameStep (k : Core) (node : Node) (f : Nat) : R Core := do
  let v ← getV k f
  let ls ← expectFrame v
  closeAt k node ls.1

/-- `assert` after the node at `pc` is read. -/
def assertStep (k : Core) (node : Node) (c : Nat) (kind : AssertKind) : R Core := do
  let cv ← getV k c
  rejectPoison cv "assert"
  assertOn k kind cv

/-- `call` after the node at `pc` is read. -/
def callStep (m : Module) (k : Core) (node : Node) (callee : Nat) (args : List Nat) : R Core := do
  let vs ← getVs k args
  callOn m k node callee vs

/-- Construct an environment without invoking its target or allocating memory.
    SemR's quoted signatures have no typed ABI descriptor; this adds no ABI
    transport claim. A bodyless target with a valid signature is constructible. -/
def makeClosureOn (m : Module) (k : Core) (node : Node) (cid target : Nat)
    (captures : List Val) : R Core :=
  match nth? m.closures cid with
  | none => tyR "MakeClosure: undefined closure type"
  | some c =>
    match nth? m.funcTys c.func with
    | none => tyR "MakeClosure: undefined apparent signature"
    | some apparent =>
      match m.functions.find? (fun f => f.id == target) with
      | none => tyR "MakeClosure: undefined function"
      | some f =>
        match nth? m.funcTys f.ty with
        | none => tyR "MakeClosure: undefined physical signature"
        | some physical =>
          if apparent.vararg || physical.vararg ||
              !(tyListEq physical.params (c.captures ++ apparent.params)) ||
              !(tyListEq physical.returns apparent.returns) then
            tyR "MakeClosure: target signature mismatch"
          else do
            checkSig m.pointerBits captures c.captures
            bindResults (next k) node [.closure cid target captures]

/-- Read the real SSA capture operands, in order, before checking construction. -/
def makeClosureStep (m : Module) (k : Core) (node : Node) (cid target : Nat)
    (captures : List Nat) : R Core := do
  let vs ← getVs k captures
  makeClosureOn m k node cid target vs

/-- `br` after the node at `pc` is read. -/
def brStep (pointerBits : Nat) (k : Core) (node : Node) (target : Nat) (args : List Nat) : R Core := do
  let vs ← getVs k args
  jump pointerBits k target vs

/-- `condBr` after the node at `pc` is read. -/
def condBrStep (pointerBits : Nat) (k : Core) (node : Node) (c tT : Nat) (tA : List Nat) (eT : Nat) (eA : List Nat) : R Core := do
  let cv ← getV k c
  rejectPoison cv "cond_br"
  branchOn pointerBits k tT tA eT eA cv

/-- `ret` after the node at `pc` is read. -/
def retStep (pointerBits : Nat) (k : Core) (node : Node) (xs : List Nat) : R Core := do
  let vs ← getVs k xs
  checkSig pointerBits vs k.sig.returns
  returnTo k vs

/-- An assumption changes the state only when its checked condition is true. -/
def assumeOn (k : Core) (node : Node) (condition : Bool) : R Core :=
  if condition then bindResults (next k) node []
  else ubR "assume condition evaluated to false: the input lies outside the assumed domain"

/-- Allocate one fresh logical cell; this is not a byte-address allocator. -/
def allocaCellStep (k : Core) (node : Node) (ty : Ty) : R Core :=
  if !isCellTy ty then unsupR "private_cell.type" else
  if (findCell k.cells k.nextCell).isSome then tyR "TypeError: private cell identity reused" else
  let c : Cell := { id := k.nextCell, ty := ty, value := .poison ty }
  bindResults { next k with cells := c :: k.cells, nextCell := k.nextCell + 1 }
    node [.cellPtr k.nextCell]
/-- A `Switch` scrutinee the fragment compares: an integer or a `Bool`. -/
def switchable : Val → Bool
  | .int _ _ => true
  | .bool _ => true
  | _ => false

/-- The jump a `Switch` takes: the matched case's target, else the default. -/
def pickOn (pointerBits : Nat) (k : Core) (dflt : Nat) (dArgs : List Nat) : Option (Nat × List Nat) → R Core
  | some (t, as) => do let vs ← getVs k as; jump pointerBits k t vs
  | none => do let vs ← getVs k dArgs; jump pointerBits k dflt vs

/-- `Switch` on its evaluated, non-poison scrutinee: an integer or `Bool`
    jumps to the first case equal to it, else to the default. -/
def switchOn (m : Module) (k : Core) (dflt : Nat) (dArgs : List Nat)
    (cases : List (Const × Nat × List Nat)) (v : Val) : R Core :=
  if switchable v then do
    let o ← switchTarget m v cases
    pickOn m.pointerBits k dflt dArgs o
  else unsupR "switch.scrutinee"

/-- `cast` after the node at `pc` is read. -/
def castStep (pointerBits : Nat) (k : Core) (node : Node) (op : CastOp) (src dst : Ty) (x : Nat) : R Core := do
  let a ← getV k x
  let v ← evalCast pointerBits op src dst a
  bindResults (next k) node [v]

/-- `switch` after the node at `pc` is read. -/
def switchStep (m : Module) (k : Core) (node : Node) (x dflt : Nat) (dArgs : List Nat)
    (cases : List (Const × Nat × List Nat)) : R Core := do
  let v ← getV k x
  rejectPoison v "switch"
  switchOn m k dflt dArgs cases v

/-- `alloca` after the node at `pc` is read. -/
def allocaStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (count al : Option Nat) : R Core := do
  let cv ← getCount k count
  let l ← layoutOf pointerBits ty
  let size ← allocSize pointerBits l.1 cv
  let align ← checkAlign (al.getD l.2)
  allocAt pointerBits k node size align

/-- `load` after the node at `pc` is read. -/
def loadStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (p : Nat) (vol : Bool) (al : Option Nat) :
    R Core := do
  let pv ← getV k p
  let size ← scalarLayout pointerBits ty
  let align ← checkAlign (al.getD size)
  let ao ← expectPtr pv "Load"
  let a ← accessAt k.mem "Load" ao.1 ao.2 size align
  readOut k node ty vol ao.2 (readBytes a.data ao.2 size)

/-- `store` after the node at `pc` is read. -/
def storeStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (p x : Nat) (vol : Bool) (al : Option Nat) :
    R Core := do
  let pv ← getV k p
  let v ← getV k x
  let size ← scalarLayout pointerBits ty
  let bs ← storeImage pointerBits ty vol size v
  let align ← checkAlign (al.getD size)
  let ao ← expectPtr pv "Store"
  let a ← accessAt k.mem "Store" ao.1 ao.2 size align
  bindResults { next k with mem := written k.mem ao.1 ao.2 a bs } node []

/-- `gep` after the node at `pc` is read. -/
def gepStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (b : Nat) (idx : List Nat) : R Core := do
  let bv ← getV k b
  let ivs ← getVs k idx
  let l ← layoutOf pointerBits ty
  let d ← gepDelta pointerBits l.1 ivs 0
  let ao ← expectPtr bv "GEP"
  gepAt pointerBits k node ao.1 ao.2 d

/-- `dealloc` after the node at `pc` is read. -/
def deallocStep (k : Core) (node : Node) (p : Nat) : R Core := do
  let pv ← getV k p
  let ao ← expectPtr pv "Dealloc"
  freeAt k node ao.1 ao.2

/-! ### The tensor map, reduction and view (`Inst::TensorMap`, `TensorReduce`, `TensorView`, wire v68)

Value-level, like `evalContract`, and shared by the executable and the
relation. Each runs the reference interpreter's checks in its order
(`crates/trust-ir/src/interpret/tensor_region.rs`): a poison operand is
undefined behaviour (`rejectPoison`, at the sites `tensor_map`,
`tensor_reduce`, `tensor_view`); the static rules on the instruction and the
operand VALUE types, then each tensor operand's well-formedness (`tensorWF`),
are type errors; the preconditions are undefined behaviour, by the
interpreter's normative messages; then the elements.

* The map (`evalMap`) evaluates its body at each coordinate, in row-major
  order, node by node through the scalar instructions' own evaluators
  (`evalBinop`, `evalUnop`, `evalIcmp`, `selectVal`, `evalCast`), whose
  verdicts are the node's; lane `i` below the operand count is operand `i`'s
  element there (or the scalar operand itself), lane `n + j` node `j`'s
  value, and the element is the last node's.
* The reduction (`evalReduce`) folds each result element from `op`'s identity,
  a left fold over the reduced multi-indices in row-major order (the first
  reduced axis outermost): `add`/`mul`/`and`/`or`/`xor` by `intBin`, the
  minima and maxima by `icmpR`'s signed or unsigned order.
* The view (`evalView`) computes over the integers (`Int`, never its division:
  `euclidDiv`/`euclidRem` are Euclidean on magnitudes), every node's value in
  `[-2^127, 2^127)`; the shape-phase nodes once, the extents, then at each
  result coordinate the index-phase nodes and the source coordinate, an
  out-of-range one reading the fill. -/

/-- A map lane's or node's type: an integer or `Bool`. -/
def mapLaneTy : Ty → Bool
  | .int _ => true
  | .bool => true
  | _ => false

/-- The type of a map node's value (`TensorMapNode::value_ty`). -/
def MapNode.valTy : MapNode → Ty
  | .binop _ ty _ _ => ty
  | .unop _ ty _ => ty
  | .icmp _ _ _ _ => .bool
  | .select ty _ _ _ => ty
  | .cast _ _ dst _ => dst

/-- Every type a map node names (`TensorMapNode::types`). -/
def MapNode.tys : MapNode → List Ty
  | .binop _ ty _ _ => [ty]
  | .unop _ ty _ => [ty]
  | .icmp _ ty _ _ => [ty]
  | .select ty _ _ _ => [ty]
  | .cast _ src dst _ => [src, dst]

/-- The lanes a map node reads, each with the type the node requires of it. -/
def MapNode.reads : MapNode → List (Nat × Ty)
  | .binop _ ty l r => [(l, ty), (r, ty)]
  | .unop _ ty x => [(x, ty)]
  | .icmp _ ty l r => [(l, ty), (r, ty)]
  | .select ty c t e => [(c, .bool), (t, ty), (e, ty)]
  | .cast _ src _ x => [(x, src)]

/-- A map lane type's width (`Ty::bit_width_with`): an integer's at
    `pointerBits`, one bit for `Bool`. -/
def mapLaneWidth (pointerBits : Nat) : Ty → Option Nat
  | .int t => some (t.bits pointerBits)
  | .bool => some 1
  | _ => none

/-- Whether a lane type is an integer. -/
def mapLaneInt : Ty → Bool
  | .int _ => true
  | _ => false

/-- Static rule M4's operation half (`TensorMapNode::op_refusal`, the one
    rule the validator and the interpreter apply): the Bool connectives only
    at `Bool`, `and`/`or`/`xor` at either lane type, every other binary and
    every unary operation at an integer; `trunc` from an integer to a
    narrower type, `zext`/`sext` to a wider integer, `bitcast` to the same
    type or between integers of one width. -/
def mapNodeOpOk (pointerBits : Nat) : MapNode → Bool
  | .binop op ty _ _ =>
    match op with
    | .bAnd | .bOr | .bXor => ty.beq .bool
    | .and | .or | .xor => true
    | _ => mapLaneInt ty
  | .unop _ ty _ => mapLaneInt ty
  | .icmp _ _ _ _ => true
  | .select _ _ _ _ => true
  | .cast op src dst _ =>
    match op, mapLaneWidth pointerBits src, mapLaneWidth pointerBits dst with
    | .trunc, some sw, some dw => mapLaneInt src && decide (dw < sw)
    | .zext, some sw, some dw => mapLaneInt dst && decide (sw < dw)
    | .sext, some sw, some dw => mapLaneInt dst && decide (sw < dw)
    | .bitcast, some sw, some dw =>
      src.beq dst || (mapLaneInt src && mapLaneInt dst && sw == dw)
    | _, _, _ => false

/-- Static rules M3/M4 over a map body, `tys` the lane types before it: each
    node names only integer and `Bool` types, reads only lanes before its
    own, each of the type it requires, and applies its operation where it
    applies (`mapNodeOpOk`). -/
def mapBodyOk (pointerBits : Nat) : List Ty → List MapNode → Bool
  | _, [] => true
  | tys, nd :: rest =>
    nd.tys.all mapLaneTy &&
      nd.reads.all (fun p => match nth? tys p.1 with
        | some t => t.beq p.2
        | none => false) &&
      mapNodeOpOk pointerBits nd &&
      mapBodyOk pointerBits (tys ++ [nd.valTy]) rest

/-- The last node's type (static rule M5 compares it with the element's). -/
def lastValTy : List MapNode → Option Ty
  | [] => none
  | [nd] => some nd.valTy
  | _ :: nds => lastValTy nds

/-- Static rule M2 on one operand: a tensor of the result's rank, or an
    integer or `Bool` scalar. -/
def mapArgOk (r : Nat) : Val → Bool
  | .tensor _ ds _ => ds.length == r
  | v => mapLaneTy v.ty

def isTensorV : Val → Bool
  | .tensor _ _ _ => true
  | _ => false

/-- An operand lane's type: a tensor's element type, or the scalar's own. -/
def mapArgTy : Val → Ty
  | .tensor e _ _ => .int e
  | v => v.ty

/-- A tensor operand's well-formedness (a scalar has none to check). -/
def mapArgWF (pointerBits : Nat) : Val → Bool
  | .tensor e ds xs => tensorWF pointerBits e ds xs
  | _ => true

/-- The first tensor operand's extents. -/
def mapDims : List Val → Option (List Nat)
  | [] => none
  | .tensor _ ds _ :: _ => some ds
  | _ :: vs => mapDims vs

/-- A tensor operand has extents `ds` (a scalar has every extent). -/
def sameDims (ds : List Nat) : Val → Bool
  | .tensor _ es _ => es == ds
  | _ => true

/-- Operand `v`'s lane at row-major position `f`: a tensor's element there, a
    scalar itself. -/
def mapLaneOf (f : Nat) : Val → Val
  | .tensor e _ xs => .int e (getN xs f)
  | v => v

/-- Each value, in order, is not poison. -/
def rejectPoisons (what : String) : List Val → R Unit
  | [] => .ok ()
  | v :: vs => do
    rejectPoison v what
    rejectPoisons what vs

/-- Each element, in order, through `f`, stopping at the first verdict. -/
def mapR {α β : Type} (f : α → R β) : List α → R (List β)
  | [] => .ok []
  | a :: as => do
    let b ← f a
    let bs ← mapR f as
    pure (b :: bs)

/-- Lane `i` of a map node's lanes. -/
def laneOf (lanes : List Val) (i : Nat) : R Val :=
  match nth? lanes i with
  | some v => .ok v
  | none => tyR "TypeError: tensor map: a node reads a lane that is not before it"

/-- `Select` at the value level, the scalar instruction's checks
    (`selectStep`, the interpreter's `eval_select`): the condition is not
    poison, both arms have the type, then the condition chooses. -/
def selectVal (pointerBits : Nat) (ty : Ty) (cv tv ev : Val) : R Val := do
  rejectPoison cv "select"
  expectTy pointerBits tv ty
  expectTy pointerBits ev ty
  match asBool cv with
  | some true => pure tv
  | some false => pure ev
  | none => tyR "TypeError: select requires a bool condition"

/-- One map node over the lanes before it, by its scalar instruction's
    evaluator. -/
def mapNodeVal (pointerBits : Nat) (lanes : List Val) : MapNode → R Val
  | .binop op ty l r => do
    let a ← laneOf lanes l
    let b ← laneOf lanes r
    evalBinop pointerBits op ty a b
  | .unop op ty x => do
    let a ← laneOf lanes x
    evalUnop pointerBits op ty a
  | .icmp op ty l r => do
    let a ← laneOf lanes l
    let b ← laneOf lanes r
    evalIcmp pointerBits op ty a b
  | .select ty c t e => do
    let cv ← laneOf lanes c
    let tv ← laneOf lanes t
    let ev ← laneOf lanes e
    selectVal pointerBits ty cv tv ev
  | .cast op src dst x => do
    let a ← laneOf lanes x
    evalCast pointerBits op src dst a

/-- The body's nodes in order, each appending its value to the lanes. -/
def mapNodes (pointerBits : Nat) : List Val → List MapNode → R (List Val)
  | lanes, [] => .ok lanes
  | lanes, nd :: rest => do
    let v ← mapNodeVal pointerBits lanes nd
    mapNodes pointerBits (lanes ++ [v]) rest

def lastVal : List Val → Option Val
  | [] => none
  | [v] => some v
  | _ :: vs => lastVal vs

/-- The map's element at row-major position `f`: the last lane, an integer of
    the element type. -/
def mapElem (pointerBits : Nat) (e : IntTy) (args : List Val) (body : List MapNode) (f : Nat) :
    R Nat := do
  let lanes ← mapNodes pointerBits (args.map (mapLaneOf f)) body
  match lastVal lanes with
  | some (.int t x) =>
    if t.code == e.code then pure x
    else tyR "TypeError: tensor map: an element is not of the element type"
  | _ => tyR "TypeError: tensor map: an element is not of the element type"

/-- `eval_tensor_map`: the checks in the interpreter's order, then the
    elements, row-major over the tensor operands' extents. -/
def evalMap (pointerBits : Nat) (ty : Ty) (args : List Val) (body : List MapNode) : R Val := do
  rejectPoisons "tensor_map" args
  match ty with
  | .tensor e r =>
    if !args.all (mapArgOk r) then
      tyR "TypeError: tensor map: an operand is neither a tensor of the result's rank nor an integer or Bool scalar"
    else if !args.any isTensorV then
      tyR "TypeError: tensor map: no operand is a tensor"
    else if body.isEmpty then
      tyR "TypeError: tensor map: the body is empty"
    else if !mapBodyOk pointerBits (args.map mapArgTy) body then
      tyR "TypeError: tensor map: a node names a type other than an integer or Bool, reads a lane not before it or of another type, or applies an operation where it does not apply"
    else if !(match lastValTy body with
        | some t => t.beq (.int e)
        | none => false) then
      tyR "TypeError: tensor map: the last node's type is not the element type"
    else if !args.all (mapArgWF pointerBits) then
      tyR "TypeError: tensor map: an operand is not a well-formed tensor"
    else
      match mapDims args with
      | none => tyR "TypeError: tensor map: no operand is a tensor"
      | some ds =>
        if !args.all (sameDims ds) then ubR "tensor map: operand extents differ"
        else do
          let xs ← mapR (mapElem pointerBits e args body) (upTo (prodL ds))
          pure (.tensor e ds xs)
  | _ => tyR "TypeError: tensor map: the result type is not a tensor type"

/-- `op`'s identity at width `w`: the value a fold over no element yields
    (`reduce_identity`). The signed extremes are the residues `2^(w-1) - 1`
    and `2^(w-1)`. -/
def reduceId (op : ReduceOp) (w : Nat) : Nat :=
  match op with
  | .add | .or | .xor | .umax => 0
  | .mul => 1
  | .and | .umin => modulus w - 1
  | .smin => half w - 1
  | .smax => half w

/-- One fold step `acc OP x` at width `w` (`reduce_step`): the wrapping and
    bitwise operators are `intBin`'s, the minima and maxima keep `acc` unless
    `x` is strictly beyond it in `icmpR`'s signed or unsigned order. -/
def reduceStep (op : ReduceOp) (w acc x : Nat) : R Nat :=
  match op with
  | .add => liftOp (intBin .add w acc x)
  | .mul => liftOp (intBin .mul w acc x)
  | .and => liftOp (intBin .and w acc x)
  | .or => liftOp (intBin .or w acc x)
  | .xor => liftOp (intBin .xor w acc x)
  | .smin => pure (if icmpR .slt w x acc then x else acc)
  | .smax => pure (if icmpR .sgt w x acc then x else acc)
  | .umin => pure (if icmpR .ult w x acc then x else acc)
  | .umax => pure (if icmpR .ugt w x acc then x else acc)

/-- The left fold of `reduceStep` from `acc` over the terms at `cs`, in order. -/
def reduceFold (op : ReduceOp) (w : Nat) (term : List Nat → Nat) : Nat → List (List Nat) → R Nat
  | acc, [] => .ok acc
  | acc, c :: cs => do
    let acc' ← reduceStep op w acc (term c)
    reduceFold op w term acc' cs

/-- The source coordinate along axis `ax` at result multi-index `o` and
    reduced multi-index `c`: a kept axis reads `o`, a reduced one `c`. -/
def reduceAxisAt (axes kept : List Nat) (o c : List Nat) (ax : Nat) : Nat :=
  match axisPos kept ax with
  | some i => getN o i
  | none =>
    match axisPos axes ax with
    | some j => getN c j
    | none => 0

/-- The result's extents: the source's at the kept axes, ascending. -/
def reduceDims (axes ds : List Nat) : List Nat :=
  (freeAxes ds.length axes).map (getN ds)

/-- Every element is above `p`, and each above the one before it. -/
def ascFrom : Nat → List Nat → Bool
  | _, [] => true
  | p, a :: as => decide (p < a) && ascFrom a as

def strictlyAscending : List Nat → Bool
  | [] => true
  | a :: as => ascFrom a as

/-- `eval_tensor_reduce`: the checks in the interpreter's order, then the
    folds, row-major over the result. -/
def evalReduce (pointerBits : Nat) (ty : Ty) (op : ReduceOp) (axes : List Nat) (a : Val) :
    R Val := do
  rejectPoison a "tensor_reduce"
  match ty, a with
  | .tensor e r, .tensor es ds xs =>
    if es.code != e.code then
      tyR "TypeError: tensor reduction: the source's element type is not the result's"
    else if !(strictlyAscending axes && axes.all (fun ax => decide (ax < ds.length))) then
      tyR "TypeError: tensor reduction: the axes are not strictly ascending axes of the source"
    else if r != ds.length - axes.length then
      tyR "TypeError: tensor reduction: the result rank is not the source's less its reduced axes"
    else if !tensorWF pointerBits e ds xs then
      tyR "TypeError: tensor reduction: the source is not a well-formed tensor"
    else if modulus pointerBits ≤ prodL (reduceDims axes ds) then
      ubR "tensor reduction: the result has more elements than usize holds"
    else do
      let w := e.bits pointerBits
      let kept := freeAxes ds.length axes
      let ys ← mapR (fun o => reduceFold op w
          (fun c => getN xs (offsetIn ds ((upTo ds.length).map (reduceAxisAt axes kept o c))))
          (reduceId op w) (multiIdx (axes.map (getN ds))))
        (multiIdx (reduceDims axes ds))
      pure (.tensor e (reduceDims axes ds) ys)
  | _, _ => tyR "TypeError: tensor reduction: the result and the source must be tensors"

/-- The node ids an arithmetic view node reads (none for an atom). -/
def IxExpr.operands : IxExpr → Option (Nat × Nat)
  | .add a b => some (a, b)
  | .sub a b => some (a, b)
  | .mul a b => some (a, b)
  | .div a b => some (a, b)
  | .rem a b => some (a, b)
  | .min a b => some (a, b)
  | .max a b => some (a, b)
  | _ => none

/-- A node's phase from its operands' (`tensor_view_index_phase`): `coord` is
    index-phase, an arithmetic node is index-phase iff an operand is, and
    every other node is shape-phase. -/
def ixPhaseOf (ph : List Bool) : IxExpr → Bool
  | .coord _ => true
  | e =>
    match e.operands with
    | some (a, b) => (nth? ph a).getD false || (nth? ph b).getD false
    | none => false

/-- Every node's phase, in id order (`ph` the phases before them). -/
def ixPhases : List Bool → List IxExpr → List Bool
  | ph, [] => ph
  | ph, e :: es => ixPhases (ph ++ [ixPhaseOf ph e]) es

/-- Static rule V5 from node `id` on: an arithmetic node reads only nodes
    before its own, `param k` names a parameter (`k < np`), `srcExtent j` a
    source axis (`j < s`) and `coord i` a result axis (`i < r`). -/
def ixScopeOk (np s r : Nat) : Nat → List IxExpr → Bool
  | _, [] => true
  | id, e :: es =>
    (match e with
      | .lit _ => true
      | .param k => decide (k < np)
      | .srcExtent j => decide (j < s)
      | .coord i => decide (i < r)
      | _ =>
        match e.operands with
        | some (a, b) => decide (a < id) && decide (b < id)
        | none => false) &&
      ixScopeOk np s r (id + 1) es

/-- An integer's magnitude. -/
def intMag : Int → Nat
  | .ofNat n => n
  | .negSucc n => n + 1

/-- The Euclidean quotient (Rust's `div_euclid`; `b ≠ 0`), spelled on
    magnitudes: `sign b · ⌊a / |b|⌋`, the floor of a negative `a` being
    `-⌈|a| / |b|⌉`. -/
def euclidDiv (a b : Int) : Int :=
  let q : Int := match a with
    | .ofNat n => ((n / intMag b : Nat) : Int)
    | .negSucc n => -(((n + intMag b) / intMag b : Nat) : Int)
  match b with
  | .negSucc _ => -q
  | .ofNat _ => q

/-- The Euclidean remainder (Rust's `rem_euclid`; `b ≠ 0`), in `[0, |b|)`. -/
def euclidRem (a b : Int) : Int :=
  match a with
  | .ofNat n => ((n % intMag b : Nat) : Int)
  | .negSucc n => (((intMag b - (n + 1) % intMag b) % intMag b : Nat) : Int)

/-- A view node's value in `[-2^127, 2^127)` (the interpreter's `i128`). -/
def ixFit (v : Int) : R Int :=
  if decide (-(half 128 : Int) ≤ v) && decide (v < (half 128 : Int)) then .ok v
  else ubR "tensor view: an index expression overflows"

/-- Node `a`'s value among those computed before it. -/
def ixAt (vals : List (Option Int)) (a : Nat) : R Int :=
  match nth? vals a with
  | some (some v) => .ok v
  | _ => tyR "TypeError: tensor view: a node reads an uncomputed node"

/-- A view node's exact value (`view_node` before its range check): `coord`
    is `none` in the shape phase, where no `coord` node is evaluated. A
    divisor of `0` is undefined behaviour. -/
def ixRaw (params : List Int) (srcDims : List Nat) (coord : Option (List Nat))
    (vals : List (Option Int)) : IxExpr → R Int
  | .lit n => .ok (n : Int)
  | .param k =>
    match nth? params k with
    | some v => .ok v
    | none => tyR "TypeError: tensor view: a node reads past its operands"
  | .srcExtent j =>
    match nth? srcDims j with
    | some d => .ok (d : Int)
    | none => tyR "TypeError: tensor view: a node reads past its operands"
  | .coord i =>
    match coord with
    | some c =>
      match nth? c i with
      | some x => .ok (x : Int)
      | none => tyR "TypeError: tensor view: a node reads past its operands"
    | none => tyR "TypeError: tensor view: a node reads past its operands"
  | .add a b => do
    let x ← ixAt vals a
    let y ← ixAt vals b
    pure (x + y)
  | .sub a b => do
    let x ← ixAt vals a
    let y ← ixAt vals b
    pure (x - y)
  | .mul a b => do
    let x ← ixAt vals a
    let y ← ixAt vals b
    pure (x * y)
  | .div a b => do
    let x ← ixAt vals a
    let y ← ixAt vals b
    if y == 0 then ubR "tensor view: an index expression divides by zero"
    else pure (euclidDiv x y)
  | .rem a b => do
    let x ← ixAt vals a
    let y ← ixAt vals b
    if y == 0 then ubR "tensor view: an index expression divides by zero"
    else pure (euclidRem x y)
  | .min a b => do
    let x ← ixAt vals a
    let y ← ixAt vals b
    pure (if x ≤ y then x else y)
  | .max a b => do
    let x ← ixAt vals a
    let y ← ixAt vals b
    pure (if x ≤ y then y else x)

/-- A view node's value: its exact value, in the `i128` range. -/
def ixNode (params : List Int) (srcDims : List Nat) (coord : Option (List Nat))
    (vals : List (Option Int)) (e : IxExpr) : R Int := do
  let v ← ixRaw params srcDims coord vals e
  ixFit v

/-- The shape phase: each shape-phase node, in id order, over the nodes
    before it (an index-phase node has no value here). -/
def viewShape (params : List Int) (srcDims : List Nat) :
    List (Option Int) → List IxExpr → List Bool → R (List (Option Int))
  | acc, e :: es, p :: ps =>
    if p then viewShape params srcDims (acc ++ [none]) es ps
    else do
      let v ← ixNode params srcDims none acc e
      viewShape params srcDims (acc ++ [some v]) es ps
  | acc, _, _ => .ok acc

/-- The index phase at result coordinate `c`: each index-phase node, in id
    order, over the nodes before it; a shape-phase node keeps its value. -/
def viewPoint (params : List Int) (srcDims : List Nat) (c : List Nat) :
    List (Option Int) → List IxExpr → List Bool → List (Option Int) → R (List (Option Int))
  | acc, e :: es, p :: ps, s :: ss =>
    if p then do
      let v ← ixNode params srcDims (some c) acc e
      viewPoint params srcDims c (acc ++ [some v]) es ps ss
    else viewPoint params srcDims c (acc ++ [s]) es ps ss
  | acc, _, _, _ => .ok acc

/-- A result extent, shape node `n`'s value: in `[0, 2^pointerBits)`. -/
def viewExtent (pointerBits : Nat) (vals : List (Option Int)) (n : Nat) : R Nat :=
  match nth? vals n with
  | some (some (.ofNat d)) =>
    if d < modulus pointerBits then .ok d
    else ubR "tensor view: a result extent does not fit usize"
  | some (some (.negSucc _)) => ubR "tensor view: a result extent does not fit usize"
  | _ => tyR "TypeError: tensor view: a result extent names no shape-phase node"

/-- The source coordinate along one axis of extent `d`: index node `n`'s
    value, `none` when it is out of range. -/
def viewSrcAxis (point : List (Option Int)) (n d : Nat) : R (Option Nat) :=
  match nth? point n with
  | some (some (.ofNat x)) => .ok (if x < d then some x else none)
  | some (some (.negSucc _)) => .ok none
  | _ => tyR "TypeError: tensor view: a source coordinate names an uncomputed node"

/-- The source coordinate, or `none` when some axis is out of range. -/
def viewSrc (point : List (Option Int)) : List Nat → List Nat → R (Option (List Nat))
  | n :: ns, d :: ds => do
    let x ← viewSrcAxis point n d
    let rest ← viewSrc point ns ds
    pure (match x, rest with
      | some x, some xs => some (x :: xs)
      | _, _ => none)
  | _, _ => .ok (some [])

/-- The view's element at result coordinate `c`. -/
def viewElem (params : List Int) (ds xs : List Nat) (exprs : List IxExpr) (phases : List Bool)
    (shapeVals : List (Option Int)) (index : List Nat) (fill : Option Nat) (c : List Nat) :
    R Nat := do
  let point ← viewPoint params ds c [] exprs phases shapeVals
  let src ← viewSrc point index ds
  match src, fill with
  | some pos, _ => pure (getN xs (offsetIn ds pos))
  | none, some f => pure f
  | none, none => ubR "tensor view: a source coordinate is out of range"

/-- A parameter's value: its `usize` residue, unsigned. -/
def viewParam : Val → R Int
  | .int _ x => .ok (x : Int)
  | _ => tyR "TypeError: tensor view: a parameter is not an integer"

/-- The fill's residue. -/
def viewFill : Option Val → R (Option Nat)
  | none => .ok none
  | some (.int _ x) => .ok (some x)
  | some _ => tyR "TypeError: tensor view: the fill is not an integer"

/-- `eval_tensor_view`: the checks in the interpreter's order, then the
    elements, row-major over the result. -/
def evalView (pointerBits : Nat) (ty : Ty) (a : Val) (ps : List Val) (exprs : List IxExpr)
    (shape index : List Nat) (fill : Option Val) : R Val := do
  rejectPoison a "tensor_view"
  rejectPoisons "tensor_view" ps
  rejectPoisons "tensor_view" fill.toList
  match ty, a with
  | .tensor e r, .tensor es ds xs =>
    let phases := ixPhases [] exprs
    if es.code != e.code then
      tyR "TypeError: tensor view: the source's element type is not the result's"
    else if !ps.all (fun p => p.ty.beq (.int .usize)) then
      tyR "TypeError: tensor view: a parameter is not a usize"
    else if !(match fill with
        | some f => f.ty.beq (.int e)
        | none => true) then
      tyR "TypeError: tensor view: the fill is not of the element type"
    else if !(shape.length == r && index.length == ds.length) then
      tyR "TypeError: tensor view: the shape and index nodes do not match the ranks"
    else if !(shape ++ index).all (fun n => decide (n < exprs.length)) then
      tyR "TypeError: tensor view: a shape or index entry names no node"
    else if !ixScopeOk ps.length ds.length r 0 exprs then
      tyR "TypeError: tensor view: a node reads out of its scope"
    else if !shape.all (fun n => !(nth? phases n).getD false) then
      tyR "TypeError: tensor view: a result extent depends on a coordinate"
    else if !tensorWF pointerBits e ds xs then
      tyR "TypeError: tensor view: the source is not a well-formed tensor"
    else do
      let pv ← mapR viewParam ps
      let fv ← viewFill fill
      let shapeVals ← viewShape pv ds [] exprs phases
      let dims ← mapR (viewExtent pointerBits shapeVals) shape
      if modulus pointerBits ≤ prodL dims then
        ubR "tensor view: the result has more elements than usize holds"
      else do
        let ys ← mapR (viewElem pv ds xs exprs phases shapeVals index fv)
          (multiIdx dims)
        pure (.tensor e dims ys)
  | _, _ => tyR "TypeError: tensor view: the result and the source must be tensors"

/-- An optional operand. -/
def getOptV (k : Core) : Option Nat → R (Option Val)
  | none => .ok none
  | some x => do
    let v ← getV k x
    pure (some v)

/-- `tensorMap` after the node at `pc` is read: the operands in order. -/
def tensorMapStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (args : List Nat)
    (body : List MapNode) : R Core := do
  let vs ← getVs k args
  let v ← evalMap pointerBits ty vs body
  bindResults (next k) node [v]

/-- `tensorReduce` after the node at `pc` is read. -/
def tensorReduceStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (src : Nat)
    (op : ReduceOp) (axes : List Nat) : R Core := do
  let a ← getV k src
  let v ← evalReduce pointerBits ty op axes a
  bindResults (next k) node [v]

/-- `tensorView` after the node at `pc` is read: the source, the parameters
    in order, then the fill. -/
def tensorViewStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (src : Nat)
    (params : List Nat) (exprs : List IxExpr) (shape index : List Nat) (fill : Option Nat) :
    R Core := do
  let a ← getV k src
  let ps ← getVs k params
  let f ← getOptV k fill
  let v ← evalView pointerBits ty a ps exprs shape index f
  bindResults (next k) node [v]

/-! ### The tensor gather and scatter (`Inst::TensorGather`, `TensorScatter`, wire v69)

Value-level, like `evalView`, and shared by the executable and the relation.
Both index a tensor in coordinate form: one COORDINATE TENSOR per axis of the
tensor they index, in axis order, each of its own integer element type. A
coordinate is read as the integer its type denotes (`coordInside`): a signed
residue at or above `half w` is negative and outside every axis, and
`isize`/`usize` have the module's pointer width. Each runs the checks in one
order, the reference interpreter's (`docs/SPEC_RATIFICATIONS.md` §26,
`crates/trust-ir/src/interpret/tensor_gather_scatter.rs`): a poison operand, in
operand order (`data`, then the coordinate tensors; `init`, `src`, then the
coordinate tensors), is undefined behaviour (`rejectPoison`, at the sites
`tensor_gather` and `tensor_scatter`); SemR has no handle value, so the
interpreter's handle check has nothing to refuse here; the static rules
G1-G3 (S1-S3) in their order, then each tensor operand's well-formedness in
operand order (`tensorWF`; a coordinate tensor at its own element type,
`mapArgWF`), are type errors; the extents precondition, then the bounds
precondition at every position (`coordsInside`), are undefined behaviour, by
the normative messages; then the elements.

* The gather (`evalGather`) has the coordinate tensors' extents and, at each
  row-major position `p`, `data`'s element at `(coords[0][p], ..)`.
* The scatter (`evalScatter`) has `init`'s extents. Every target is decided
  before any element is written; then, from `init`'s elements, each source
  position `p` in row-major order writes `src`'s element at `(coords[0][p],
  ..)` (`scatterWrites`), so where several positions name one coordinate the
  row-major-last write is the one the result holds. -/

/-- A coordinate, the residue `x` of a coordinate tensor's element of type
    `t`, read as the integer `t` denotes, is inside an axis of extent `d`:
    `0 ≤ x < d`. A signed residue at or above `half w` is negative, outside
    every axis. -/
def coordInside (pointerBits : Nat) (t : IntTy) (d x : Nat) : Bool :=
  !(t.signed && isNeg (t.bits pointerBits) x) && decide (x < d)

/-- Static rules G3/S3 on one coordinate operand: a tensor of rank `r` (a
    tensor's element is always an integer). -/
def coordRankOk (r : Nat) : Val → Bool
  | .tensor _ ds _ => ds.length == r
  | _ => false

/-- The coordinate the coordinate tensors hold at row-major position `f`,
    one per axis of the extents `ds` they index, in axis order; `none` when
    one is outside its axis. -/
def coordsAt (pointerBits f : Nat) : List Val → List Nat → Option (List Nat)
  | .tensor t _ xs :: cs, d :: ds =>
    if coordInside pointerBits t d (getN xs f) then
      (coordsAt pointerBits f cs ds).map (getN xs f :: ·)
    else none
  | [], [] => some []
  | _, _ => none

/-- The bounds precondition: at every row-major position below `n`, every
    coordinate is inside its axis of `ds`. -/
def coordsInside (pointerBits : Nat) (coords : List Val) (ds : List Nat) (n : Nat) : Bool :=
  (upTo n).all (fun f => (coordsAt pointerBits f coords ds).isSome)

/-- The row-major offset, in a tensor of extents `ds`, of the coordinate at
    position `f` (`0` where one is outside its axis, which the bounds
    precondition has refused before any element is read). -/
def coordOffset (pointerBits : Nat) (coords : List Val) (ds : List Nat) (f : Nat) : Nat :=
  match coordsAt pointerBits f coords ds with
  | some pos => offsetIn ds pos
  | none => 0

/-- The scatter's writes in row-major source order: each source residue over
    `acc` at its target offset, so a later write at one offset replaces an
    earlier one. -/
def scatterWrites : List Nat → List Nat → List Nat → List Nat
  | acc, t :: ts, y :: ys => scatterWrites (setNth acc t y) ts ys
  | acc, _, _ => acc

/-- `eval_tensor_gather`: the checks in §26's order, then the elements,
    row-major over the coordinate tensors' extents. -/
def evalGather (pointerBits : Nat) (ty : Ty) (data : Val) (coords : List Val) : R Val := do
  rejectPoison data "tensor_gather"
  rejectPoisons "tensor_gather" coords
  match ty, data with
  | .tensor e r, .tensor ed ds xs =>
    if ed.code != e.code then
      tyR "TypeError: tensor gather: the data's element type is not the result's"
    else if ds.isEmpty || coords.length != ds.length then
      tyR "TypeError: tensor gather: the data has rank 0, or the coordinate operands are not one per data axis"
    else if !coords.all (coordRankOk r) then
      tyR "TypeError: tensor gather: a coordinate operand is not an integer tensor of the result's rank"
    else if !tensorWF pointerBits e ds xs then
      tyR "TypeError: tensor gather: the data is not a well-formed tensor"
    else if !coords.all (mapArgWF pointerBits) then
      tyR "TypeError: tensor gather: a coordinate tensor is not a well-formed tensor"
    else
      match mapDims coords with
      | none => tyR "TypeError: tensor gather: no coordinate operand is a tensor"
      | some cds =>
        if !coords.all (sameDims cds) then
          ubR "tensor gather: coordinate tensors have different extents"
        else if !coordsInside pointerBits coords ds (prodL cds) then
          ubR "tensor gather: a coordinate is outside its axis"
        else
          pure (.tensor e cds ((upTo (prodL cds)).map (fun f =>
            getN xs (coordOffset pointerBits coords ds f))))
  | _, _ => tyR "TypeError: tensor gather: the result and the data must be tensors"

/-- `eval_tensor_scatter`: the checks in §26's order, then the writes, in
    row-major source order, over `init`'s elements. -/
def evalScatter (pointerBits : Nat) (ty : Ty) (init src : Val) (coords : List Val) : R Val := do
  rejectPoison init "tensor_scatter"
  rejectPoison src "tensor_scatter"
  rejectPoisons "tensor_scatter" coords
  match ty, init, src with
  | .tensor e s, .tensor ei di xi, .tensor es ds ys =>
    if !(ei.code == e.code && di.length == s) then
      tyR "TypeError: tensor scatter: init is not of the result type"
    else if es.code != e.code then
      tyR "TypeError: tensor scatter: the source's element type is not the result's"
    else if s == 0 || coords.length != s then
      tyR "TypeError: tensor scatter: the result has rank 0, or the coordinate operands are not one per result axis"
    else if !coords.all (coordRankOk ds.length) then
      tyR "TypeError: tensor scatter: a coordinate operand is not an integer tensor of the source's rank"
    else if !tensorWF pointerBits e di xi then
      tyR "TypeError: tensor scatter: init is not a well-formed tensor"
    else if !tensorWF pointerBits e ds ys then
      tyR "TypeError: tensor scatter: the source is not a well-formed tensor"
    else if !coords.all (mapArgWF pointerBits) then
      tyR "TypeError: tensor scatter: a coordinate tensor is not a well-formed tensor"
    else if !coords.all (sameDims ds) then
      ubR "tensor scatter: coordinate tensor extents differ from the source's"
    else if !coordsInside pointerBits coords di (prodL ds) then
      ubR "tensor scatter: a coordinate is outside its axis"
    else
      pure (.tensor e di (scatterWrites xi
        ((upTo (prodL ds)).map (coordOffset pointerBits coords di)) ys))
  | _, _, _ => tyR "TypeError: tensor scatter: the result, init and the source must be tensors"

/-- A repeated coordinate keeps the row-major-last write: `[7, 9]` scattered
    at `[1, 1]` over `[0, 0, 0]` leaves `9` at `1`. -/
theorem scatter_repeated_coordinate_keeps_the_last_write :
    evalScatter 64 (.tensor .u8 1) (.tensor .u8 [3] [0, 0, 0]) (.tensor .u8 [2] [7, 9])
      [.tensor .usize [2] [1, 1]] = .ok (.tensor .u8 [3] [0, 9, 0]) := rfl

/-- A negative signed coordinate is outside every axis: `-1` at `i8` (residue
    `255`) indexes no element of a three-element axis. -/
theorem gather_negative_coordinate_is_outside :
    evalGather 64 (.tensor .u8 1) (.tensor .u8 [3] [4, 5, 6]) [.tensor .i8 [1] [255]] =
      ubR "tensor gather: a coordinate is outside its axis" := rfl

/-- A coordinate at its axis's extent is outside it, at the scatter too. -/
theorem scatter_coordinate_at_the_extent_is_outside :
    evalScatter 64 (.tensor .u8 1) (.tensor .u8 [3] [0, 0, 0]) (.tensor .u8 [1] [7])
      [.tensor .u32 [1] [3]] = ubR "tensor scatter: a coordinate is outside its axis" := rfl

/-- A gather of a rank-2 tensor at two coordinate tensors: `[[1, 2], [3, 4]]`
    at `(1, 0)` and `(0, 1)` reads `[3, 2]`. -/
theorem gather_reads_the_named_elements :
    evalGather 64 (.tensor .i32 1) (.tensor .i32 [2, 2] [1, 2, 3, 4])
      [.tensor .u8 [2] [1, 0], .tensor .i64 [2] [0, 1]] = .ok (.tensor .i32 [2] [3, 2]) := rfl

/-- `tensorGather` after the node at `pc` is read: the data, then the
    coordinate tensors in order. -/
def tensorGatherStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (data : Nat)
    (coords : List Nat) : R Core := do
  let d ← getV k data
  let cs ← getVs k coords
  let v ← evalGather pointerBits ty d cs
  bindResults (next k) node [v]

/-- `tensorScatter` after the node at `pc` is read: `init`, the source, then
    the coordinate tensors in order. -/
def tensorScatterStep (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (init src : Nat)
    (coords : List Nat) : R Core := do
  let a ← getV k init
  let s ← getV k src
  let cs ← getVs k coords
  let v ← evalScatter pointerBits ty a s cs
  bindResults (next k) node [v]

/-- Execute one instruction node of the current block. -/
def execNode (m : Module) (k : Core) (node : Node) : StepR :=
  match node.inst with
  | .binop op ty l r => ofR (binopStep m.pointerBits k node op ty l r)
  | .unop op ty x => ofR (unopStep m.pointerBits k node op ty x)
  | .overflow op ty l r => ofR (overflowStep m.pointerBits k node op ty l r)
  | .icmp op ty l r => ofR (icmpStep m.pointerBits k node op ty l r)
  | .const ty c => ofR (constStep m k node ty c)
  | .copy ty x => ofR (copyStep m.pointerBits k node ty x)
  | .select ty c t e => ofR (selectStep m.pointerBits k node ty c t e)
  | .extractField ty agg field => ofR (extractFieldStep m k node ty agg field)
  | .insertField ty agg field x => ofR (insertFieldStep m k node ty agg field x)
  | .undef ty => ofR do
    let v ← undefVal ty
    bindResults (next k) node [v]
  | .assume c => ofR do
    let cv ← getV k c
    let b ← expectBool cv
    assumeOn k node b
  | .allocaCell ty => ofR (allocaCellStep k node ty)
  | .loadCell ty x => ofR do
    let ptr ← getV k x
    let c ← expectCell k ptr ty
    expectTy m.pointerBits c.value ty
    bindResults (next k) node [c.value]
  | .storeCell ty x value => ofR do
    let ptr ← getV k x
    let c ← expectCell k ptr ty
    let v ← getV k value
    expectTy m.pointerBits v ty
    bindResults { next k with cells := putCell k.cells { c with value := v } } node []
  | .openFrame slots =>
    ofR (bindResults { next k with openFrames := k.nextFrame :: k.openFrames,
                                   nextFrame := k.nextFrame + 1 }
      node [.frame k.nextFrame (slots.map (fun _ => none))])
  | .bindSlot f slot x => ofR (bindSlotStep k node f slot x)
  | .loadSlot f slot ty => ofR (loadSlotStep m.pointerBits k node f slot ty)
  | .closeFrame f => ofR (closeFrameStep k node f)
  | .nullPtr => ofR (bindResults (next k) node [.nullPtr])
  | .unreachable => .done (.ub "executed unreachable")
  | .assert c kind => ofR (assertStep k node c kind)
  | .call callee args => ofR (callStep m k node callee args)
  | .makeClosure cid target captures => ofR (makeClosureStep m k node cid target captures)
  | .br target args => ofR (brStep m.pointerBits k node target args)
  | .condBr c tT tA eT eA => ofR (condBrStep m.pointerBits k node c tT tA eT eA)
  | .cast op src dst x => ofR (castStep m.pointerBits k node op src dst x)
  | .switch x dflt dArgs cases => ofR (switchStep m k node x dflt dArgs cases)
  | .ret xs => ofR (retStep m.pointerBits k node xs)
  | .alloca ty count al => ofR (allocaStep m.pointerBits k node ty count al)
  | .load ty p vol al => ofR (loadStep m.pointerBits k node ty p vol al)
  | .store ty p x vol al => ofR (storeStep m.pointerBits k node ty p x vol al)
  | .gep ty b idx => ofR (gepStep m.pointerBits k node ty b idx)
  | .dealloc p => ofR (deallocStep k node p)
  | .tensorContract ty l r batch contract =>
    ofR (tensorContractStep m.pointerBits k node ty l r batch contract)
  | .tensorMap ty args body => ofR (tensorMapStep m.pointerBits k node ty args body)
  | .tensorReduce ty src op axes => ofR (tensorReduceStep m.pointerBits k node ty src op axes)
  | .tensorView ty src params exprs shape index fill =>
    ofR (tensorViewStep m.pointerBits k node ty src params exprs shape index fill)
  | .tensorGather ty data coords => ofR (tensorGatherStep m.pointerBits k node ty data coords)
  | .tensorScatter ty init src coords =>
    ofR (tensorScatterStep m.pointerBits k node ty init src coords)

/-- One step: the node at `pc`, or the missing-terminator refusal. -/
def stepCore (m : Module) (k : Core) : StepR :=
  match nth? k.block.body k.pc with
  | none => .done (.typeError "MalformedInstruction: block ended without a terminator")
  | some node => execNode m k node

/-! ## The small-step relation

`Step m k r`: from state `k`, one step of module `m` ends in `r` (a next
state, or a verdict). It is stated rule by rule, one rule per instruction
and outcome, and nowhere mentions the executable (`stepCore`, `execNode`,
`ofR` or the pieces above): each rule names the node at `pc`, the values its
operands read, and the state the step moves to (the program counter, the SSA
environment, the open binding frames and the lineage counter, the call stack
and the call depth), spelled out in the rule itself.

What the relation trusts. It is independent of the executable in its control
and state transitions: every check that reads or moves the machine state —
that a frame's lineage is open (`Opened`), nominal closure metadata and
physical target signatures (`MakesClosure`), the signature check at a call or
return boundary (`SigChecks`), and the binding of block parameters on a jump
or call entry (`ParamsBind`) — is stated by the relation's own rules, not by
the executable's helpers (`openedAt`, `checkSig`, `bindParams`), and a
mutant of one of those helpers no longer kernel-checks. It SHARES with the
executable the helpers that compute a value from values: the environment
lookup `getV`/`getVs`, the type and shape checks `expectTy`, `expectFrame`,
`rejectPoison` and `asBool`, the operators (`evalBinop`, `evalUnop`,
`evalIcmp`, `evalOverflow`; the residue layer `intBin`/`intUn`/`icmpR`/`ovf`
is equated with MiniRust's in `SemRMiniRust.lean`), the constant, field and
message builders `constVal`, `evalExtract`, `evalInsert` and
`assertMessage`, the tensor contraction `evalContract` (with its shape and
element helpers `contractAxesOk`, `tensorWF`, `contractDims`,
`contractElems`, `multiIdx`, `axisAt`, `offsetIn`, `macR`), the v68 map,
reduction and view `evalMap`, `evalReduce` and `evalView` (with their static
rules, `selectVal`, `reduceStep`, `reduceFold`, the view's node evaluation
`ixNode`, `euclidDiv`, `euclidRem` and its phases, and the optional-operand
read `getOptV`), the v69 gather and scatter `evalGather` and `evalScatter`
(with their static rules, the coordinate reading `coordInside`, `coordsAt`,
`coordsInside` and `coordOffset`, and the ordered writes `scatterWrites`),
the v70 content-addressed tensor `blobVal` (with the table lookup
`blobRow`, the digest `sha256` and its rounds, schedule and padding
`shaRound`, `shaSchedule`, `shaBlock`, `shaPad`, and the little-endian
element reading `leChunks`, `leNat`), and the list helpers `nth?`, `setNth`, `findBlock`,
`memNat` and `removeNat`. The memory rules are the same split: what reads
or moves the memory — an allocation's existence, liveness, address, alignment
and bounds (`Accesses`), the uninitialized bytes of a load (`Reads`), a new
allocation's id, address and the bump past it (`Allocates`), a `Dealloc`'s
base and liveness (`Frees`) and a `GEP`'s offset bound (`Offsets`) — is the
relation's own, while the value helpers are shared: the layouts and
alignments (`layoutOf`, `scalarLayout`, `checkAlign`, `alignUp`), the pointer
check `expectPtr`, the byte list helpers (`byteAt`, `readBytes`, `setByte`,
`writeBytes`, `uninitBytes`, `firstUninit`), the encoding (`leBytes`,
`fromLE`, `encodeVal`, `decodeVal`, `storeImage`) and the operand arithmetic
(`getCount`, `allocSize`, `gepDelta`). A drift in one of those changes the
relation and the executable together; trust-ir's SemR differential against
`interpret.rs` is what checks them (and `SemRMemory.lean` the laws they
obey).

A helper's failure stops the step with the helper's verdict (`Seq.stop`),
the left-to-right order of the premises being the order the reference
interpreter checks them in. `step_sound` and `step_complete` prove the
executable `stepCore` is exactly this relation, so `run` (below) is held to
the rules, not to itself. -/

/-- Premise sequencing: `x` yields `a` and the rest `P a` ends in `r`, or `x`
    stops with verdict `o` and so does the step. -/
inductive Seq {α : Type} (x : R α) (P : α → StepR → Prop) : StepR → Prop where
  | ok (a : α) (r : StepR) : x = .ok a → P a r → Seq x P r
  | stop (o : Out) : x = .stop o → Seq x P (.done o)

/-- A step through the frame of lineage `l` continues (`P`) only while `l`
    is open; a handle of a lineage that is not open is undefined behaviour. -/
inductive Opened (k : Core) (what : String) (l : Nat) (P : StepR → Prop) : StepR → Prop where
  | isOpen (r : StepR) : memNat k.openFrames l = true → P r → Opened k what l P r
  | closed : memNat k.openFrames l = false →
      Opened k what l P (.done (.ub s!"{what}: frame is not open"))

/-- The signature check of a call or return boundary: each value, in order,
    is not poison and has its declared type, and there are as many values as
    types; then the step continues (`P`). -/
inductive SigChecks (pointerBits : Nat) (P : StepR → Prop) : List Val → List Ty → StepR → Prop where
  | done (r : StepR) : P r → SigChecks pointerBits P [] [] r
  | next (v : Val) (vs : List Val) (t : Ty) (ts : List Ty) (r : StepR) :
      rejectPoison v "signature boundary" = .ok () → v.ty.beq t = true →
      expectTy pointerBits v t = .ok () →
      SigChecks pointerBits P vs ts r → SigChecks pointerBits P (v :: vs) (t :: ts) r
  | poison (v : Val) (vs : List Val) (t : Ty) (ts : List Ty) (o : Out) :
      rejectPoison v "signature boundary" = .stop o → SigChecks pointerBits P (v :: vs) (t :: ts) (.done o)
  | wrongTy (v : Val) (vs : List Val) (t : Ty) (ts : List Ty) :
      rejectPoison v "signature boundary" = .ok () → v.ty.beq t = false →
      SigChecks pointerBits P (v :: vs) (t :: ts) (.done (.typeError "SignatureMismatch: type mismatch"))
  | invalidValue (v : Val) (vs : List Val) (t : Ty) (ts : List Ty) (o : Out) :
      rejectPoison v "signature boundary" = .ok () → v.ty.beq t = true →
      expectTy pointerBits v t = .stop o →
      SigChecks pointerBits P (v :: vs) (t :: ts) (.done o)
  | tooMany (v : Val) (vs : List Val) :
      SigChecks pointerBits P (v :: vs) [] (.done (.typeError "SignatureMismatch: arity mismatch"))
  | tooFew (t : Ty) (ts : List Ty) :
      SigChecks pointerBits P [] (t :: ts) (.done (.typeError "SignatureMismatch: arity mismatch"))

/-- Binding block parameters `ps` to values over environment `env`: each
    parameter `(x, t)` in order binds `x` to its value, latest first, when the
    value has type `t`, and the step continues with the environment that
    results (`P`); an arity mismatch is a type error. -/
inductive ParamsBind (pointerBits : Nat) (P : List (Nat × Val) → StepR → Prop) :
    List (Nat × Val) → List (Nat × Ty) → List Val → StepR → Prop where
  | done (env : List (Nat × Val)) (r : StepR) : P env r → ParamsBind pointerBits P env [] [] r
  | bind (env : List (Nat × Val)) (x : Nat) (t : Ty) (ps : List (Nat × Ty)) (v : Val)
      (vs : List Val) (r : StepR) :
      expectTy pointerBits v t = .ok () → ParamsBind pointerBits P ((x, v) :: env) ps vs r →
      ParamsBind pointerBits P env ((x, t) :: ps) (v :: vs) r
  | wrongTy (env : List (Nat × Val)) (x : Nat) (t : Ty) (ps : List (Nat × Ty)) (v : Val)
      (vs : List Val) (o : Out) :
      expectTy pointerBits v t = .stop o → ParamsBind pointerBits P env ((x, t) :: ps) (v :: vs) (.done o)
  | tooFew (env : List (Nat × Val)) (p : Nat × Ty) (ps : List (Nat × Ty)) :
      ParamsBind pointerBits P env (p :: ps) []
        (.done (.typeError "MalformedInstruction: block parameter arity mismatch"))
  | tooMany (env : List (Nat × Val)) (v : Val) (vs : List Val) :
      ParamsBind pointerBits P env [] (v :: vs)
        (.done (.typeError "MalformedInstruction: block parameter arity mismatch"))

/-- The declared results `results` bind the produced values, latest first,
    in the state `k` the step moves to; an arity mismatch is a type error. -/
inductive Binds (k : Core) (results : List Nat) (vs : List Val) : StepR → Prop where
  | ok : (results.length != vs.length) = false →
      Binds k results vs (.cont { k with env := (results.zip vs).reverse ++ k.env })
  | arity : (results.length != vs.length) = true →
      Binds k results vs (.done (.typeError "MalformedInstruction: instruction result arity mismatch"))

/-- The state transitions of an evaluated assumption. -/
inductive Assumes (k : Core) (results : List Nat) : Bool → StepR → Prop where
  | pass (r : StepR) : Binds (next k) results [] r → Assumes k results true r
  | fail : Assumes k results false
      (.done (.ub "assume condition evaluated to false: the input lies outside the assumed domain"))

/-- Allocation states its type/freshness checks and the exact shared-cell
    update independently of the executable allocation helper. -/
inductive CellAlloc (k : Core) (results : List Nat) (ty : Ty) : StepR → Prop where
  | unsupported : isCellTy ty = false →
      CellAlloc k results ty (.done (.unsupported "private_cell.type"))
  | reused : isCellTy ty = true → (findCell k.cells k.nextCell).isSome = true →
      CellAlloc k results ty (.done (.typeError "TypeError: private cell identity reused"))
  | fresh (r : StepR) : isCellTy ty = true → (findCell k.cells k.nextCell).isSome = false →
      Binds { next k with
        cells := { id := k.nextCell, ty := ty, value := .poison ty } :: k.cells,
        nextCell := k.nextCell + 1 } results [.cellPtr k.nextCell] r →
      CellAlloc k results ty r

/-- A private-cell address states its lookup and type checks directly. The
    poison guard is sequenced separately, before these address rules. -/
inductive CellAddress (k : Core) (ptr : Val) (ty : Ty) (P : Cell → StepR → Prop) :
    StepR → Prop where
  | notPtr : (∀ id, ptr ≠ .cellPtr id) →
      CellAddress k ptr ty P (.done (.typeError "TypeError: expected a private cell address"))
  | missing (id : Nat) : ptr = .cellPtr id → findCell k.cells id = none →
      CellAddress k ptr ty P (.done (.ub "private cell address has no allocation"))
  | wrongTy (id : Nat) (c : Cell) : ptr = .cellPtr id → findCell k.cells id = some c →
      c.ty.beq ty = false →
      CellAddress k ptr ty P (.done (.typeError "TypeError: private cell access type mismatch"))
  | unsupported (id : Nat) (c : Cell) : ptr = .cellPtr id → findCell k.cells id = some c →
      c.ty.beq ty = true → isCellTy ty = false →
      CellAddress k ptr ty P (.done (.unsupported "private_cell.type"))
  | ready (id : Nat) (c : Cell) (r : StepR) :
      ptr = .cellPtr id → findCell k.cells id = some c →
      c.ty.beq ty = true → isCellTy ty = true → P c r → CellAddress k ptr ty P r

/-- A jump pointerBits to block `target` of the running function with arguments `args`:
    the block's parameters are bound over the current environment and the
    block runs from its first node. -/
inductive Jumps (pointerBits : Nat) (k : Core) (target : Nat) (args : List Val) : StepR → Prop where
  | missing : findBlock k.fn.blocks target = none →
      Jumps pointerBits k target args (.done (.typeError "MissingBlock: block not found"))
  | enter (b : Block) (r : StepR) : findBlock k.fn.blocks target = some b →
      ParamsBind pointerBits (fun env r => r = .cont { k with block := b, pc := 0, env := env })
        k.env b.params args r →
      Jumps pointerBits k target args r

/-- `Select` on its evaluated condition. -/
inductive Selects (k : Core) (results : List Nat) (tv ev cv : Val) : StepR → Prop where
  | yes (hb : asBool cv = some true) (r : StepR) : Binds (next k) results [tv] r →
      Selects k results tv ev cv r
  | no (hb : asBool cv = some false) (r : StepR) : Binds (next k) results [ev] r →
      Selects k results tv ev cv r
  | notBool : asBool cv = none →
      Selects k results tv ev cv (.done (.typeError "TypeError: select requires a bool condition"))

/-- `BindSlot` of `v` into slot `slot` of the open frame `(l, s)`. -/
inductive SlotWrite (k : Core) (results : List Nat) (l : Nat) (s : List (Option Val)) (slot : Nat)
    (v : Val) : StepR → Prop where
  | range : s.length ≤ slot →
      SlotWrite k results l s slot v (.done (.ub "BindSlot: slot out of range"))
  | write (h : ¬ s.length ≤ slot) (r : StepR) :
      Binds (next k) results [.frame l (setNth s slot (some v))] r →
      SlotWrite k results l s slot v r

/-- `LoadSlot` at type `ty` from slot contents `s`. An unbound scalar slot
    reads poison. -/
inductive SlotRead (pointerBits : Nat) (k : Core) (results : List Nat) (slot : Nat) (ty : Ty) (s : List (Option Val)) :
    StepR → Prop where
  | range : nth? s slot = none →
      SlotRead pointerBits k results slot ty s (.done (.ub "LoadSlot: slot out of range"))
  | bound (v : Val) (r : StepR) : nth? s slot = some (some v) →
      Seq (expectTy pointerBits v ty) (fun _ => Binds (next k) results [v]) r → SlotRead pointerBits k results slot ty s r
  | poison (hs : nth? s slot = some none) (hsc : isScalarTy ty = true) (r : StepR) :
      Binds (next k) results [.poison ty] r → SlotRead pointerBits k results slot ty s r
  | nonScalar : nth? s slot = some none → isScalarTy ty = false →
      SlotRead pointerBits k results slot ty s (.done (.ub "LoadSlot: poison of a non-scalar type"))

/-- `CloseFrame` of lineage `l`: only an open frame closes, once. -/
inductive Closes (k : Core) (results : List Nat) (l : Nat) : StepR → Prop where
  | close (hm : memNat k.openFrames l = true) (r : StepR) :
      Binds { next k with openFrames := removeNat k.openFrames l } results [] r →
      Closes k results l r
  | twice : memNat k.openFrames l = false →
      Closes k results l (.done (.ub "CloseFrame: frame is not open (double close)"))

/-- `Assert` on its evaluated condition: `true` continues, `false` panics
    with the kind's message. -/
inductive Asserts (k : Core) (kind : AssertKind) (cv : Val) : StepR → Prop where
  | pass : asBool cv = some true → Asserts k kind cv (.cont (next k))
  | fail (hb : asBool cv = some false) (r : StepR) :
      Seq (assertMessage k kind) (fun msg r => r = .done (.panic msg)) r →
      Asserts k kind cv r
  | notBool : asBool cv = none →
      Asserts k kind cv (.done (.typeError "TypeError: assert requires bool"))

/-- `CondBr` on its evaluated condition. -/
inductive Branches (pointerBits : Nat) (k : Core) (tT : Nat) (tA : List Nat) (eT : Nat) (eA : List Nat) (cv : Val) :
    StepR → Prop where
  | yes (hb : asBool cv = some true) (r : StepR) :
      Seq (getVs k tA) (fun vs => Jumps pointerBits k tT vs) r → Branches pointerBits k tT tA eT eA cv r
  | no (hb : asBool cv = some false) (r : StepR) :
      Seq (getVs k eA) (fun vs => Jumps pointerBits k eT vs) r → Branches pointerBits k tT tA eT eA cv r
  | notBool : asBool cv = none →
      Branches pointerBits k tT tA eT eA cv (.done (.typeError "TypeError: cond_br requires bool"))

/-- The jump a `Switch` takes once its case is chosen: to the matched case's
    target with its arguments, else to the default with its own. -/
inductive Picks (pointerBits : Nat) (k : Core) (dflt : Nat) (dArgs : List Nat) :
    Option (Nat × List Nat) → StepR → Prop where
  | case (t : Nat) (as : List Nat) (r : StepR) :
      Seq (getVs k as) (fun vs => Jumps pointerBits k t vs) r → Picks pointerBits k dflt dArgs (some (t, as)) r
  | dflt (r : StepR) :
      Seq (getVs k dArgs) (fun vs => Jumps pointerBits k dflt vs) r → Picks pointerBits k dflt dArgs none r

/-- `Switch` on its evaluated scrutinee `v`: an integer or `Bool` is compared
    with the cases in order (`switchTarget`), anything else is refused by name. -/
inductive Switches (m : Module) (k : Core) (dflt : Nat) (dArgs : List Nat)
    (cases : List (Const × Nat × List Nat)) (v : Val) : StepR → Prop where
  | scalar (hv : switchable v = true) (r : StepR) :
      Seq (switchTarget m v cases) (fun o => Picks m.pointerBits k dflt dArgs o) r →
      Switches m k dflt dArgs cases v r
  | other : switchable v = false →
      Switches m k dflt dArgs cases v (.done (.unsupported "switch.scrutinee"))

/-- Entering callee `f` (signature `sig`) on `vs`: its entry block runs with
    its parameters bound in a fresh environment, one level deeper, the caller
    (`k` at the call node `node`) suspended on the stack. A body-less callee
    is a declaration. -/
inductive Enters (pointerBits : Nat) (k : Core) (node : Node) (f : Func) (sig : FuncTy) (vs : List Val) :
    StepR → Prop where
  | decl : f.blocks.isEmpty = true →
      Enters pointerBits k node f sig vs (.done (.unsupported "interprocedural_call"))
  | noEntry : f.blocks.isEmpty = false → findBlock f.blocks f.entry = none →
      Enters pointerBits k node f sig vs (.done (.typeError "MissingBlock: entry block not found"))
  | push (b : Block) (r : StepR) : f.blocks.isEmpty = false → findBlock f.blocks f.entry = some b →
      ParamsBind pointerBits
        (fun env r => r = .cont
          { fn := f, sig := sig, block := b, pc := 0, env := env, depth := k.depth - 1,
            stack := { fn := k.fn, sig := k.sig, block := k.block, pc := k.pc, env := k.env,
                       depth := k.depth, node := node } :: k.stack,
            openFrames := k.openFrames, nextFrame := k.nextFrame,
            cells := k.cells, nextCell := k.nextCell, mem := k.mem }) [] b.params vs r →
      Enters pointerBits k node f sig vs r

/-- A direct call of function `callee` on the evaluated arguments `vs`. -/
inductive Calls (m : Module) (k : Core) (node : Node) (callee : Nat) (vs : List Val) :
    StepR → Prop where
  | depth : (k.depth == 0) = true → Calls m k node callee vs (.done .outOfFuel)
  | noFn : (k.depth == 0) = false → m.functions.find? (fun f => f.id == callee) = none →
      Calls m k node callee vs (.done (.typeError "MissingFunction: undefined function"))
  | noSig (f : Func) : (k.depth == 0) = false →
      m.functions.find? (fun f => f.id == callee) = some f → nth? m.funcTys f.ty = none →
      Calls m k node callee vs (.done (.typeError "SignatureMismatch: undefined signature"))
  | varargDecl (f : Func) (sig : FuncTy) : (k.depth == 0) = false →
      m.functions.find? (fun f => f.id == callee) = some f → nth? m.funcTys f.ty = some sig →
      sig.vararg = true → f.blocks.isEmpty = true →
      Calls m k node callee vs (.done (.unsupported "call.vararg"))
  | varargDef (f : Func) (sig : FuncTy) : (k.depth == 0) = false →
      m.functions.find? (fun f => f.id == callee) = some f → nth? m.funcTys f.ty = some sig →
      sig.vararg = true → f.blocks.isEmpty = false →
      Calls m k node callee vs (.done (.typeError "SignatureMismatch: variadic definition"))
  | enter (f : Func) (sig : FuncTy) (r : StepR) : (k.depth == 0) = false →
      m.functions.find? (fun f => f.id == callee) = some f → nth? m.funcTys f.ty = some sig →
      sig.vararg = false → SigChecks m.pointerBits (Enters m.pointerBits k node f sig vs) vs sig.params r →
      Calls m k node callee vs r

/-- `Return` of the checked values `vs`: from the outermost call the run
    ends with them; otherwise the caller resumes AFTER its call node, in its
    own function, block, environment and depth, with the node's results bound
    to them. -/
inductive Returns (k : Core) (vs : List Val) : StepR → Prop where
  | top : k.stack = [] → Returns k vs (.done (.ret vs))
  | pop (c : Caller) (rest : List Caller) (r : StepR) : k.stack = c :: rest →
      Binds { fn := c.fn, sig := c.sig, block := c.block, pc := c.pc + 1, env := c.env,
              depth := c.depth, stack := rest, openFrames := k.openFrames,
              nextFrame := k.nextFrame, cells := k.cells, nextCell := k.nextCell, mem := k.mem }
        c.node.results vs r →
      Returns k vs r

/-- An access of `size` bytes with alignment `align` through the pointer
    `(a, o)` in memory `mem` continues (`P`, with the allocation's record) only
    when the allocation exists and is live, the address `base + o` fits and is
    a multiple of `align`, the end `o + size` fits, and the bytes
    `[o, o + size)` lie inside the allocation; each failure is undefined
    behaviour, checked in that order (`rangeOverflow`, the end that does not
    fit, is never reached in a run: see `accessAlloc`). -/
inductive Accesses (mem : Mem) (op : String) (a o size align : Nat) (P : Alloc → StepR → Prop) :
    StepR → Prop where
  | unknown : nth? mem.allocs a = none →
      Accesses mem op a o size align P (.done (.ub s!"{op}: unknown allocation {decStr a}"))
  | dead (al : Alloc) : nth? mem.allocs a = some al → al.live = false →
      Accesses mem op a o size align P (.done (.ub s!"{op}: use after dealloc"))
  | addrOverflow (al : Alloc) : nth? mem.allocs a = some al → al.live = true →
      decide (addrSpace ≤ al.base + o) = true →
      Accesses mem op a o size align P (.done (.ub s!"{op}: pointer address overflow"))
  | misaligned (al : Alloc) : nth? mem.allocs a = some al → al.live = true →
      decide (addrSpace ≤ al.base + o) = false → ((al.base + o) % align != 0) = true →
      Accesses mem op a o size align P
        (.done (.ub s!"{op}: pointer address {decStr (al.base + o)} is not aligned to {decStr align}"))
  | rangeOverflow (al : Alloc) : nth? mem.allocs a = some al → al.live = true →
      decide (addrSpace ≤ al.base + o) = false → ((al.base + o) % align != 0) = false →
      decide (addrSpace ≤ o + size) = true →
      Accesses mem op a o size align P (.done (.ub s!"{op}: access range overflow"))
  | outOfBounds (al : Alloc) : nth? mem.allocs a = some al → al.live = true →
      decide (addrSpace ≤ al.base + o) = false → ((al.base + o) % align != 0) = false →
      decide (addrSpace ≤ o + size) = false → decide (al.size < o + size) = true →
      Accesses mem op a o size align P
        (.done (.ub s!"{op}: access [{decStr o}..{decStr (o + size)}) is out of bounds for allocation size {decStr al.size}"))
  | ok (al : Alloc) (r : StepR) : nth? mem.allocs a = some al → al.live = true →
      decide (addrSpace ≤ al.base + o) = false → ((al.base + o) % align != 0) = false →
      decide (addrSpace ≤ o + size) = false → decide (al.size < o + size) = false →
      P al r → Accesses mem op a o size align P r

/-- A `Load` at type `ty` that read the bytes `bs` (at offset `o`): bytes all
    initialized are the value they decode to; a plain load of bytes with an
    uninitialized one reads them as poison, a volatile load is undefined
    behaviour at the first such byte. -/
inductive Reads (k : Core) (results : List Nat) (ty : Ty) (vol : Bool) (o : Nat) (bs : List AByte) :
    StepR → Prop where
  | init (hf : firstUninit bs = none) (r : StepR) :
      Seq (decodeVal ty bs) (fun v => Binds (next k) results [v]) r → Reads k results ty vol o bs r
  | strict (i : Nat) : firstUninit bs = some i → vol = true →
      Reads k results ty vol o bs (.done (.ub s!"Load: reading uninitialized byte at offset {decStr (o + i)}"))
  | poison (i : Nat) (r : StepR) : firstUninit bs = some i → vol = false →
      Binds (next k) results [.partialBytes ty bs] r → Reads k results ty vol o bs r

/-- An allocation of `size` bytes aligned to `align`: it is allocation number
    `k.mem.allocs.length`, live, uninitialized, at the next free address
    rounded up to `align`, the next free address past it (by one when
    `size = 0`), and the step binds a pointer to its first byte; an address
    past `2^64` is out of memory. -/
inductive Allocates (pointerBits : Nat) (k : Core) (results : List Nat) (size align : Nat) : StepR → Prop where
  | oomAlign : decide (addrSpace ≤ k.mem.nextAddr + (align - 1)) = true →
      Allocates pointerBits k results size align (.done .outOfMemory)
  | oomEnd : decide (addrSpace ≤ k.mem.nextAddr + (align - 1)) = false →
      decide (addrSpace ≤ alignUp k.mem.nextAddr align + max size 1) = true →
      Allocates pointerBits k results size align (.done .outOfMemory)
  | oomTarget : decide (addrSpace ≤ k.mem.nextAddr + (align - 1)) = false →
      decide (addrSpace ≤ alignUp k.mem.nextAddr align + max size 1) = false →
      decide (2 ^ pointerBits < alignUp k.mem.nextAddr align + max size 1) = true →
      Allocates pointerBits k results size align (.done .outOfMemory)
  | fresh (h1 : decide (addrSpace ≤ k.mem.nextAddr + (align - 1)) = false)
      (h2 : decide (addrSpace ≤ alignUp k.mem.nextAddr align + max size 1) = false)
      (ht : decide (2 ^ pointerBits < alignUp k.mem.nextAddr align + max size 1) = false) (r : StepR) :
      Binds { next k with
              mem := { allocs := k.mem.allocs ++
                         [{ base := alignUp k.mem.nextAddr align, size := size, align := align,
                            live := true, data := [] }],
                       nextAddr := alignUp k.mem.nextAddr align + max size 1 } }
        results [.ptr k.mem.allocs.length 0] r →
      Allocates pointerBits k results size align r

/-- `Dealloc` through `(a, o)`: the base of a live allocation, which becomes
    dead (it stays in the memory, so a stale pointer still names it); an
    interior pointer, an unknown or a dead allocation is undefined behaviour. -/
inductive Frees (k : Core) (results : List Nat) (a o : Nat) : StepR → Prop where
  | interior : (o != 0) = true →
      Frees k results a o (.done (.ub "Dealloc: pointer must reference allocation base"))
  | unknown : (o != 0) = false → nth? k.mem.allocs a = none →
      Frees k results a o (.done (.ub s!"Dealloc: unknown allocation {decStr a}"))
  | dead (al : Alloc) : (o != 0) = false → nth? k.mem.allocs a = some al → al.live = false →
      Frees k results a o (.done (.ub "Dealloc: allocation is already dead"))
  | free (al : Alloc) (r : StepR) : (o != 0) = false → nth? k.mem.allocs a = some al →
      al.live = true →
      Binds { next k with
              mem := { k.mem with allocs := setNth k.mem.allocs a { al with live := false } } }
        results [] r →
      Frees k results a o r

/-- The pointer a `GEP` binds: allocation `a`, offset `o + d`, when it fits. -/
inductive Offsets (pointerBits : Nat) (k : Core) (results : List Nat) (a o d : Nat) : StepR → Prop where
  | overflow : decide (addrSpace ≤ o + d) = true →
      Offsets pointerBits k results a o d (.done (.ub "GEP: pointer offset overflow"))
  | wide (h : decide (addrSpace ≤ o + d) = false) (hw : (pointerBits != 64) = false) (r : StepR) :
      Binds (next k) results [.ptr a (o + d)] r → Offsets pointerBits k results a o d r
  | unknown : decide (addrSpace ≤ o + d) = false → (pointerBits != 64) = true →
      nth? k.mem.allocs a = none →
      Offsets pointerBits k results a o d (.done (.ub s!"GEP: unknown allocation {decStr a}"))
  | baseOverflow (al : Alloc) : decide (addrSpace ≤ o + d) = false → (pointerBits != 64) = true →
      nth? k.mem.allocs a = some al →
      (decide (addrSpace ≤ al.base + o) || decide (2 ^ pointerBits ≤ al.base + o)) = true →
      Offsets pointerBits k results a o d (.done (.ub "GEP: pointer address overflow"))
  | addressOverflow (al : Alloc) : decide (addrSpace ≤ o + d) = false → (pointerBits != 64) = true →
      nth? k.mem.allocs a = some al →
      (decide (addrSpace ≤ al.base + o) || decide (2 ^ pointerBits ≤ al.base + o)) = false →
      decide (addrSpace ≤ al.base + o + d) = true →
      Offsets pointerBits k results a o d (.done (.ub "GEP: pointer offset overflow"))
  | outside (al : Alloc) : decide (addrSpace ≤ o + d) = false → (pointerBits != 64) = true →
      nth? k.mem.allocs a = some al →
      (decide (addrSpace ≤ al.base + o) || decide (2 ^ pointerBits ≤ al.base + o)) = false →
      decide (addrSpace ≤ al.base + o + d) = false → decide (2 ^ pointerBits ≤ al.base + o + d) = true →
      Offsets pointerBits k results a o d (.done (.ub
        s!"GEP: address {hexStr (al.base + o + d)} is outside the target's address space (highest address {hexStr (2 ^ pointerBits - 1)})"))
  | ok (al : Alloc) (h : decide (addrSpace ≤ o + d) = false) (hw : (pointerBits != 64) = true)
      (hn : nth? k.mem.allocs a = some al)
      (hb : (decide (addrSpace ≤ al.base + o) || decide (2 ^ pointerBits ≤ al.base + o)) = false)
      (hu : decide (addrSpace ≤ al.base + o + d) = false)
      (ht : decide (2 ^ pointerBits ≤ al.base + o + d) = false) (r : StepR) :
      Binds (next k) results [.ptr a (o + d)] r → Offsets pointerBits k results a o d r

/-- Nominal construction stated independently of makeClosureOn: each table
    lookup, physical signature check, capture check and result binding is a
    premise, with its own refusal outcome. Construction never enters a body. -/
inductive MakesClosure (m : Module) (k : Core) (results : List Nat)
    (cid target : Nat) (captures : List Val) : StepR → Prop where
  | noClosure : nth? m.closures cid = none →
      MakesClosure m k results cid target captures
        (.done (.typeError "MakeClosure: undefined closure type"))
  | noApparent (c : ClosureTy) : nth? m.closures cid = some c →
      nth? m.funcTys c.func = none → MakesClosure m k results cid target captures
        (.done (.typeError "MakeClosure: undefined apparent signature"))
  | noFunction (c : ClosureTy) (apparent : FuncTy) :
      nth? m.closures cid = some c → nth? m.funcTys c.func = some apparent →
      m.functions.find? (fun f => f.id == target) = none →
      MakesClosure m k results cid target captures
        (.done (.typeError "MakeClosure: undefined function"))
  | noPhysical (c : ClosureTy) (apparent : FuncTy) (f : Func) :
      nth? m.closures cid = some c → nth? m.funcTys c.func = some apparent →
      m.functions.find? (fun f => f.id == target) = some f →
      nth? m.funcTys f.ty = none → MakesClosure m k results cid target captures
        (.done (.typeError "MakeClosure: undefined physical signature"))
  | mismatch (c : ClosureTy) (apparent : FuncTy) (f : Func) (physical : FuncTy) :
      nth? m.closures cid = some c → nth? m.funcTys c.func = some apparent →
      m.functions.find? (fun f => f.id == target) = some f →
      nth? m.funcTys f.ty = some physical →
      (apparent.vararg || physical.vararg ||
        !(tyListEq physical.params (c.captures ++ apparent.params)) ||
        !(tyListEq physical.returns apparent.returns)) = true →
      MakesClosure m k results cid target captures
        (.done (.typeError "MakeClosure: target signature mismatch"))
  | checked (c : ClosureTy) (apparent : FuncTy) (f : Func) (physical : FuncTy) (r : StepR) :
      nth? m.closures cid = some c → nth? m.funcTys c.func = some apparent →
      m.functions.find? (fun f => f.id == target) = some f →
      nth? m.funcTys f.ty = some physical →
      (apparent.vararg || physical.vararg ||
        !(tyListEq physical.params (c.captures ++ apparent.params)) ||
        !(tyListEq physical.returns apparent.returns)) = false →
      SigChecks m.pointerBits (Binds (next k) results [.closure cid target captures])
        captures c.captures r → MakesClosure m k results cid target captures r

/-- One step of module `m` from state `k`, by the instruction at `pc`. -/
inductive Step (m : Module) (k : Core) : StepR → Prop where
  | noTerminator : nth? k.block.body k.pc = none →
      Step m k (.done (.typeError "MalformedInstruction: block ended without a terminator"))
  | binop (results : List Nat) (op : BinOp) (ty : Ty) (l r : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .binop op ty l r, results := results } →
      Seq (getV k l) (fun a => Seq (getV k r) (fun b =>
        Seq (evalBinop m.pointerBits op ty a b) (fun v => Binds (next k) results [v]))) res →
      Step m k res
  | unop (results : List Nat) (op : UnOp) (ty : Ty) (x : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .unop op ty x, results := results } →
      Seq (getV k x) (fun a => Seq (evalUnop m.pointerBits op ty a) (fun v => Binds (next k) results [v])) res →
      Step m k res
  | overflow (results : List Nat) (op : OvfOp) (ty : Ty) (l r : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .overflow op ty l r, results := results } →
      Seq (getV k l) (fun a => Seq (getV k r) (fun b =>
        Seq (evalOverflow m.pointerBits op ty a b) (fun vs => Binds (next k) results vs))) res →
      Step m k res
  | icmp (results : List Nat) (op : ICmpOp) (ty : Ty) (l r : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .icmp op ty l r, results := results } →
      Seq (getV k l) (fun a => Seq (getV k r) (fun b =>
        Seq (evalIcmp m.pointerBits op ty a b) (fun v => Binds (next k) results [v]))) res →
      Step m k res
  | const (results : List Nat) (ty : Ty) (c : Const) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .const ty c, results := results } →
      Seq (constVal m 8 ty c) (fun v => Binds (next k) results [v]) res →
      Step m k res
  | copy (results : List Nat) (ty : Ty) (x : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .copy ty x, results := results } →
      Seq (getV k x) (fun a => Seq (expectTy m.pointerBits a ty) (fun _ => Binds (next k) results [a])) res →
      Step m k res
  | select (results : List Nat) (ty : Ty) (c t e : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .select ty c t e, results := results } →
      Seq (getV k c) (fun cv => Seq (getV k t) (fun tv => Seq (getV k e) (fun ev =>
        Seq (rejectPoison cv "select") (fun _ => Seq (expectTy m.pointerBits tv ty) (fun _ =>
          Seq (expectTy m.pointerBits ev ty) (fun _ => Selects k results tv ev cv)))))) res →
      Step m k res
  | extractField (results : List Nat) (ty : Ty) (agg field : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .extractField ty agg field, results := results } →
      Seq (getV k agg) (fun a => Seq (evalExtract m ty a field) (fun v =>
        Binds (next k) results [v])) res →
      Step m k res
  | insertField (results : List Nat) (ty : Ty) (agg field x : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .insertField ty agg field x, results := results } →
      Seq (getV k agg) (fun a => Seq (getV k x) (fun v => Seq (evalInsert m ty a field v)
        (fun w => Binds (next k) results [w]))) res →
      Step m k res
  | undef (results : List Nat) (ty : Ty) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .undef ty, results := results } →
      Seq (undefVal ty) (fun v => Binds (next k) results [v]) res → Step m k res
  | assume (results : List Nat) (c : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .assume c, results := results } →
      Seq (getV k c) (fun cv => Seq (expectBool cv) (fun b => Assumes k results b)) res →
      Step m k res
  | allocaCell (results : List Nat) (ty : Ty) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .allocaCell ty, results := results } →
      CellAlloc k results ty res → Step m k res
  | loadCell (results : List Nat) (ty : Ty) (x : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .loadCell ty x, results := results } →
      Seq (getV k x) (fun ptr => Seq (rejectPoison ptr "private cell address")
        (fun _ => CellAddress k ptr ty (fun c => Seq (expectTy m.pointerBits c.value ty)
          (fun _ => Binds (next k) results [c.value])))) res → Step m k res
  | storeCell (results : List Nat) (ty : Ty) (x value : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .storeCell ty x value, results := results } →
      Seq (getV k x) (fun ptr => Seq (rejectPoison ptr "private cell address")
        (fun _ => CellAddress k ptr ty (fun c => Seq (getV k value) (fun v =>
          Seq (expectTy m.pointerBits v ty) (fun _ =>
            Binds { next k with cells := putCell k.cells { c with value := v } }
              results []))))) res → Step m k res
  | openFrame (results : List Nat) (slots : List Ty) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .openFrame slots, results := results } →
      Binds { next k with openFrames := k.nextFrame :: k.openFrames, nextFrame := k.nextFrame + 1 }
        results [.frame k.nextFrame (slots.map (fun _ => none))] res →
      Step m k res
  | bindSlot (results : List Nat) (f slot x : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .bindSlot f slot x, results := results } →
      Seq (getV k f) (fun h => Seq (expectFrame h) (fun ls => Opened k "BindSlot" ls.1
        (Seq (getV k x) (fun v => SlotWrite k results ls.1 ls.2 slot v)))) res →
      Step m k res
  | loadSlot (results : List Nat) (f slot : Nat) (ty : Ty) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .loadSlot f slot ty, results := results } →
      Seq (getV k f) (fun h => Seq (expectFrame h) (fun ls => Opened k "LoadSlot" ls.1
        (SlotRead m.pointerBits k results slot ty ls.2))) res →
      Step m k res
  | closeFrame (results : List Nat) (f : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .closeFrame f, results := results } →
      Seq (getV k f) (fun v => Seq (expectFrame v) (fun ls => Closes k results ls.1)) res →
      Step m k res
  | nullPtr (results : List Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .nullPtr, results := results } →
      Binds (next k) results [.nullPtr] res → Step m k res
  | unreachable (results : List Nat) :
      nth? k.block.body k.pc = some { inst := .unreachable, results := results } →
      Step m k (.done (.ub "executed unreachable"))
  | assert (results : List Nat) (c : Nat) (kind : AssertKind) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .assert c kind, results := results } →
      Seq (getV k c) (fun cv => Seq (rejectPoison cv "assert") (fun _ => Asserts k kind cv)) res →
      Step m k res
  | makeClosure (results : List Nat) (cid target : Nat) (captures : List Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .makeClosure cid target captures, results := results } →
      Seq (getVs k captures) (fun vs => MakesClosure m k results cid target vs) res →
      Step m k res
  | call (results : List Nat) (callee : Nat) (args : List Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .call callee args, results := results } →
      Seq (getVs k args)
        (fun vs => Calls m k { inst := .call callee args, results := results } callee vs) res →
      Step m k res
  | br (results : List Nat) (target : Nat) (args : List Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .br target args, results := results } →
      Seq (getVs k args) (fun vs => Jumps m.pointerBits k target vs) res →
      Step m k res
  | condBr (results : List Nat) (c tT : Nat) (tA : List Nat) (eT : Nat) (eA : List Nat)
      (res : StepR) :
      nth? k.block.body k.pc = some { inst := .condBr c tT tA eT eA, results := results } →
      Seq (getV k c) (fun cv => Seq (rejectPoison cv "cond_br") (fun _ =>
        Branches m.pointerBits k tT tA eT eA cv)) res →
      Step m k res
  | cast (results : List Nat) (op : CastOp) (src dst : Ty) (x : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .cast op src dst x, results := results } →
      Seq (getV k x) (fun a => Seq (evalCast m.pointerBits op src dst a) (fun v => Binds (next k) results [v])) res →
      Step m k res
  | switch (results : List Nat) (x dflt : Nat) (dArgs : List Nat)
      (cases : List (Const × Nat × List Nat)) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .switch x dflt dArgs cases, results := results } →
      Seq (getV k x) (fun v => Seq (rejectPoison v "switch") (fun _ =>
        Switches m k dflt dArgs cases v)) res →
      Step m k res
  | ret (results : List Nat) (xs : List Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .ret xs, results := results } →
      Seq (getVs k xs) (fun vs => SigChecks m.pointerBits (Returns k vs) vs k.sig.returns) res →
      Step m k res
  | alloca (results : List Nat) (ty : Ty) (count al : Option Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .alloca ty count al, results := results } →
      Seq (getCount k count) (fun cv => Seq (layoutOf m.pointerBits ty) (fun l => Seq (allocSize m.pointerBits l.1 cv)
        (fun size => Seq (checkAlign (al.getD l.2)) (fun align =>
          Allocates m.pointerBits k results size align)))) res →
      Step m k res
  | load (results : List Nat) (ty : Ty) (p : Nat) (vol : Bool) (al : Option Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .load ty p vol al, results := results } →
      Seq (getV k p) (fun pv => Seq (scalarLayout m.pointerBits ty) (fun size => Seq (checkAlign (al.getD size))
        (fun align => Seq (expectPtr pv "Load") (fun ao =>
          Accesses k.mem "Load" ao.1 ao.2 size align (fun a =>
            Reads k results ty vol ao.2 (readBytes a.data ao.2 size)))))) res →
      Step m k res
  | store (results : List Nat) (ty : Ty) (p x : Nat) (vol : Bool) (al : Option Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .store ty p x vol al, results := results } →
      Seq (getV k p) (fun pv => Seq (getV k x) (fun v => Seq (scalarLayout m.pointerBits ty) (fun size =>
        Seq (storeImage m.pointerBits ty vol size v) (fun bs => Seq (checkAlign (al.getD size)) (fun align =>
          Seq (expectPtr pv "Store") (fun ao =>
            Accesses k.mem "Store" ao.1 ao.2 size align (fun a =>
              Binds { next k with
                      mem := { k.mem with
                               allocs := setNth k.mem.allocs ao.1
                                 { a with data := writeBytes a.data ao.2 bs } } }
                results []))))))) res →
      Step m k res
  | gep (results : List Nat) (ty : Ty) (b : Nat) (idx : List Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .gep ty b idx, results := results } →
      Seq (getV k b) (fun bv => Seq (getVs k idx) (fun ivs => Seq (layoutOf m.pointerBits ty) (fun l =>
        Seq (gepDelta m.pointerBits l.1 ivs 0) (fun d => Seq (expectPtr bv "GEP") (fun ao =>
          Offsets m.pointerBits k results ao.1 ao.2 d))))) res →
      Step m k res
  | dealloc (results : List Nat) (p : Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .dealloc p, results := results } →
      Seq (getV k p) (fun pv => Seq (expectPtr pv "Dealloc") (fun ao => Frees k results ao.1 ao.2)) res →
      Step m k res
  | tensorContract (results : List Nat) (ty : Ty) (l r : Nat) (batch contract : List (Nat × Nat))
      (res : StepR) :
      nth? k.block.body k.pc = some { inst := .tensorContract ty l r batch contract, results := results } →
      Seq (getV k l) (fun a => Seq (getV k r) (fun b =>
        Seq (evalContract m.pointerBits ty batch contract a b) (fun v =>
          Binds (next k) results [v]))) res →
      Step m k res
  | tensorMap (results : List Nat) (ty : Ty) (args : List Nat) (body : List MapNode)
      (res : StepR) :
      nth? k.block.body k.pc = some { inst := .tensorMap ty args body, results := results } →
      Seq (getVs k args) (fun vs =>
        Seq (evalMap m.pointerBits ty vs body) (fun v =>
          Binds (next k) results [v])) res →
      Step m k res
  | tensorReduce (results : List Nat) (ty : Ty) (src : Nat) (op : ReduceOp) (axes : List Nat)
      (res : StepR) :
      nth? k.block.body k.pc = some { inst := .tensorReduce ty src op axes, results := results } →
      Seq (getV k src) (fun a =>
        Seq (evalReduce m.pointerBits ty op axes a) (fun v =>
          Binds (next k) results [v])) res →
      Step m k res
  | tensorView (results : List Nat) (ty : Ty) (src : Nat) (params : List Nat)
      (exprs : List IxExpr) (shape index : List Nat) (fill : Option Nat) (res : StepR) :
      nth? k.block.body k.pc =
        some { inst := .tensorView ty src params exprs shape index fill, results := results } →
      Seq (getV k src) (fun a => Seq (getVs k params) (fun ps => Seq (getOptV k fill) (fun f =>
        Seq (evalView m.pointerBits ty a ps exprs shape index f) (fun v =>
          Binds (next k) results [v])))) res →
      Step m k res
  | tensorGather (results : List Nat) (ty : Ty) (data : Nat) (coords : List Nat) (res : StepR) :
      nth? k.block.body k.pc = some { inst := .tensorGather ty data coords, results := results } →
      Seq (getV k data) (fun d => Seq (getVs k coords) (fun cs =>
        Seq (evalGather m.pointerBits ty d cs) (fun v =>
          Binds (next k) results [v]))) res →
      Step m k res
  | tensorScatter (results : List Nat) (ty : Ty) (init src : Nat) (coords : List Nat)
      (res : StepR) :
      nth? k.block.body k.pc =
        some { inst := .tensorScatter ty init src coords, results := results } →
      Seq (getV k init) (fun a => Seq (getV k src) (fun s => Seq (getVs k coords) (fun cs =>
        Seq (evalScatter m.pointerBits ty a s cs) (fun v =>
          Binds (next k) results [v])))) res →
      Step m k res

/-! ### The executable step is the relation

Each piece's lemma pair says the piece's executable result satisfies its
relation (`*_complete`) and that the relation has no other result
(`*_sound`); `step_complete`/`step_sound` compose them. -/

/-- A bind on a value continues with it. -/
theorem ok_bind {α β : Type} (a : α) (f : α → R β) : (R.ok a >>= f) = f a := rfl

/-- Completeness of a sequenced premise: when the rest of the executable
    satisfies `P` for every value, the bind satisfies `Seq`. -/
theorem seq_of_bind {α : Type} (x : R α) (f : α → R Core) (P : α → StepR → Prop)
    (h : ∀ a, P a (ofR (f a))) : Seq x P (ofR (x >>= f)) := by
  cases hx : x with
  | ok a => exact Seq.ok a _ rfl (h a)
  | stop o => exact Seq.stop o rfl

/-- Soundness of a sequenced premise. -/
theorem bind_of_seq {α : Type} (x : R α) (f : α → R Core) (P : α → StepR → Prop) (r : StepR)
    (h : ∀ a r, P a r → ofR (f a) = r) (hs : Seq x P r) : ofR (x >>= f) = r := by
  cases hs with
  | ok a r hx hp => rw [hx]; exact h a r hp
  | stop o hx => rw [hx]; rfl

theorem opened_complete (k : Core) (what : String) (l : Nat) (P : StepR → Prop) (c : R Core)
    (h : P (ofR c)) : Opened k what l P (ofR (openedAt k l what c)) := by
  unfold openedAt
  cases hm : memNat k.openFrames l
  · exact @Opened.closed k what l P hm
  · exact @Opened.isOpen k what l P _ hm h

theorem opened_sound (k : Core) (what : String) (l : Nat) (P : StepR → Prop) (c : R Core)
    (r : StepR) (h : ∀ r, P r → ofR c = r) (ho : Opened k what l P r) :
    ofR (openedAt k l what c) = r := by
  unfold openedAt
  cases ho with
  | isOpen r hm hp => rw [hm]; exact h r hp
  | closed hm => rw [hm]; rfl

theorem checkSig_cons (pointerBits : Nat) (v : Val) (vs : List Val) (t : Ty) (ts : List Ty) :
    checkSig pointerBits (v :: vs) (t :: ts) = (do
    rejectPoison v "signature boundary"
    if v.ty.beq t then do
      expectTy pointerBits v t
      checkSig pointerBits vs ts
    else tyR "SignatureMismatch: type mismatch") := rfl

theorem sigChecks_complete (pointerBits : Nat) (P : StepR → Prop) (f : Unit → R Core) :
    ∀ (vs : List Val) (ts : List Ty), (∀ u, P (ofR (f u))) →
      SigChecks pointerBits P vs ts (ofR (checkSig pointerBits vs ts >>= f)) := by
  intro vs
  induction vs with
  | nil =>
    intro ts h
    cases ts with
    | nil => exact @SigChecks.done pointerBits P _ (h ())
    | cons t ts => exact @SigChecks.tooFew pointerBits P t ts
  | cons v vs ih =>
    intro ts h
    cases ts with
    | nil => exact @SigChecks.tooMany pointerBits P v vs
    | cons t ts =>
      rw [checkSig_cons]
      cases hp : rejectPoison v "signature boundary" with
      | stop o => exact @SigChecks.poison pointerBits P v vs t ts o hp
      | ok u =>
        cases u
        rw [ok_bind]
        cases hb : v.ty.beq t with
        | true =>
          cases he : expectTy pointerBits v t with
          | stop o => exact @SigChecks.invalidValue pointerBits P v vs t ts o hp hb he
          | ok u =>
            cases u
            exact @SigChecks.next pointerBits P v vs t ts _ hp hb he (ih ts h)
        | false => exact @SigChecks.wrongTy pointerBits P v vs t ts hp hb

theorem sigChecks_sound (pointerBits : Nat) (P : StepR → Prop) (f : Unit → R Core) (h : ∀ u r, P r → ofR (f u) = r)
    (vs : List Val) (ts : List Ty) (r : StepR) (hs : SigChecks pointerBits P vs ts r) :
    ofR (checkSig pointerBits vs ts >>= f) = r := by
  induction hs with
  | done r hr => exact h () r hr
  | next v vs t ts r hp hb he _ ih =>
    rw [checkSig_cons, hp, ok_bind, hb, he, ok_bind]; exact ih
  | poison v vs t ts o hp => rw [checkSig_cons, hp]; rfl
  | wrongTy v vs t ts hp hb => rw [checkSig_cons, hp, ok_bind, hb]; rfl
  | invalidValue v vs t ts o hp hb he =>
    rw [checkSig_cons, hp, ok_bind, hb, he]; rfl
  | tooMany v vs => rfl
  | tooFew t ts => rfl

theorem bindParams_cons (pointerBits : Nat) (env : List (Nat × Val)) (x : Nat) (t : Ty) (ps : List (Nat × Ty)) (v : Val)
    (vs : List Val) :
    bindParams pointerBits env ((x, t) :: ps) (v :: vs) = (do
    expectTy pointerBits v t
    bindParams pointerBits ((x, v) :: env) ps vs) := rfl

theorem paramsBind_complete (pointerBits : Nat) (P : List (Nat × Val) → StepR → Prop) (f : List (Nat × Val) → R Core) :
    ∀ (ps : List (Nat × Ty)) (env : List (Nat × Val)) (vs : List Val), (∀ e, P e (ofR (f e))) →
      ParamsBind pointerBits P env ps vs (ofR (bindParams pointerBits env ps vs >>= f)) := by
  intro ps
  induction ps with
  | nil =>
    intro env vs h
    cases vs with
    | nil => exact @ParamsBind.done pointerBits P env _ (h env)
    | cons v vs => exact @ParamsBind.tooMany pointerBits P env v vs
  | cons p ps ih =>
    intro env vs h
    cases p with
    | mk x t =>
      cases vs with
      | nil => exact @ParamsBind.tooFew pointerBits P env (x, t) ps
      | cons v vs =>
        rw [bindParams_cons]
        cases he : expectTy pointerBits v t with
        | stop o => exact @ParamsBind.wrongTy pointerBits P env x t ps v vs o he
        | ok u =>
          cases u
          rw [ok_bind]
          exact @ParamsBind.bind pointerBits P env x t ps v vs _ he (ih _ _ h)

theorem paramsBind_sound (pointerBits : Nat) (P : List (Nat × Val) → StepR → Prop) (f : List (Nat × Val) → R Core)
    (h : ∀ e r, P e r → ofR (f e) = r) (env : List (Nat × Val)) (ps : List (Nat × Ty))
    (vs : List Val) (r : StepR) (hp : ParamsBind pointerBits P env ps vs r) :
    ofR (bindParams pointerBits env ps vs >>= f) = r := by
  induction hp with
  | done env r hr => exact h env r hr
  | bind env x t ps v vs r he _ ih => rw [bindParams_cons, he, ok_bind]; exact ih
  | wrongTy env x t ps v vs o he => rw [bindParams_cons, he]; rfl
  | tooFew env p ps => cases p; rfl
  | tooMany env v vs => rfl

theorem binds_complete (k : Core) (node : Node) (vs : List Val) :
    Binds k node.results vs (ofR (bindResults k node vs)) := by
  unfold bindResults
  cases h : (node.results.length != vs.length)
  · exact Binds.ok h
  · exact Binds.arity h

theorem binds_sound (k : Core) (node : Node) (vs : List Val) (r : StepR)
    (h : Binds k node.results vs r) : ofR (bindResults k node vs) = r := by
  unfold bindResults
  cases h with
  | ok h => rw [h]; rfl
  | arity h => rw [h]; rfl

theorem jumps_complete (pointerBits : Nat) (k : Core) (target : Nat) (args : List Val) :
    Jumps pointerBits k target args (ofR (jump pointerBits k target args)) := by
  unfold jump
  cases hb : findBlock k.fn.blocks target with
  | none => exact Jumps.missing hb
  | some b => exact Jumps.enter b _ hb (paramsBind_complete pointerBits _ _ _ _ _ (fun _ => rfl))

theorem jumps_sound (pointerBits : Nat) (k : Core) (target : Nat) (args : List Val) (r : StepR)
    (h : Jumps pointerBits k target args r) : ofR (jump pointerBits k target args) = r := by
  unfold jump
  cases h with
  | missing hb => rw [hb]; rfl
  | enter b r hb hs =>
    rw [hb]
    exact paramsBind_sound pointerBits _ _ (fun _ r h => h.symm) _ _ _ _ hs

theorem assumes_complete (k : Core) (node : Node) (condition : Bool) :
    Assumes k node.results condition (ofR (assumeOn k node condition)) := by
  cases condition with
  | false => exact Assumes.fail
  | true => exact Assumes.pass _ (binds_complete _ _ _)

theorem assumes_sound (k : Core) (node : Node) (condition : Bool) (r : StepR)
    (h : Assumes k node.results condition r) : ofR (assumeOn k node condition) = r := by
  cases h with
  | pass r hb => exact binds_sound _ _ _ _ hb
  | fail => rfl

theorem cellAlloc_complete (k : Core) (node : Node) (ty : Ty) :
    CellAlloc k node.results ty (ofR (allocaCellStep k node ty)) := by
  unfold allocaCellStep
  cases ht : isCellTy ty with
  | false => exact CellAlloc.unsupported ht
  | true =>
    cases hf : (findCell k.cells k.nextCell).isSome with
    | false => exact CellAlloc.fresh _ ht hf (binds_complete _ _ _)
    | true => exact CellAlloc.reused ht hf

theorem cellAlloc_sound (k : Core) (node : Node) (ty : Ty) (r : StepR)
    (h : CellAlloc k node.results ty r) : ofR (allocaCellStep k node ty) = r := by
  unfold allocaCellStep
  cases h with
  | unsupported ht => rw [ht]; rfl
  | reused ht hf => rw [ht, hf]; rfl
  | fresh r ht hf hb => rw [ht, hf]; exact binds_sound _ _ _ _ hb

theorem cellAddress_complete (k : Core) (ptr : Val) (ty : Ty)
    (P : Cell → StepR → Prop) (f : Cell → R Core) (h : ∀ c, P c (ofR (f c))) :
    CellAddress k ptr ty P (ofR (cellAddress k ptr ty >>= f)) := by
  cases ptr with
  | int t raw => exact CellAddress.notPtr (by intro id he; cases he)
  | bool b => exact CellAddress.notPtr (by intro id he; cases he)
  | nullPtr => exact CellAddress.notPtr (by intro id he; cases he)
  | enum id lanes => exact CellAddress.notPtr (by intro other he; cases he)
  | struct id lanes => exact CellAddress.notPtr (by intro other he; cases he)
  | closure id target captures => exact CellAddress.notPtr (by intro other he; cases he)
  | unwritten t => exact CellAddress.notPtr (by intro id he; cases he)
  | frame id slots => exact CellAddress.notPtr (by intro other he; cases he)
  | poison t => exact CellAddress.notPtr (by intro id he; cases he)
  | ptr alloc offset => exact CellAddress.notPtr (by intro id he; cases he)
  | partialBytes t bytes => exact CellAddress.notPtr (by intro id he; cases he)
  | tensor e dims elems => exact CellAddress.notPtr (by intro id he; cases he)
  | cellPtr id =>
    simp only [cellAddress]
    cases hf : findCell k.cells id with
    | none => exact CellAddress.missing id rfl hf
    | some c =>
      simp only [hf]
      cases ht : c.ty.beq ty with
      | false => exact CellAddress.wrongTy id c rfl hf ht
      | true =>
        cases hs : isCellTy ty with
        | false => exact CellAddress.unsupported id c rfl hf ht hs
        | true => exact CellAddress.ready id c _ rfl hf ht hs (h c)

theorem cellAddress_sound (k : Core) (ptr : Val) (ty : Ty)
    (P : Cell → StepR → Prop) (f : Cell → R Core)
    (h : ∀ c r, P c r → ofR (f c) = r) (r : StepR) (hc : CellAddress k ptr ty P r) :
    ofR (cellAddress k ptr ty >>= f) = r := by
  cases hc with
  | notPtr hp =>
    cases ptr <;> try rfl
    exact False.elim (hp _ rfl)
  | missing id hp hf => rw [hp]; simp [cellAddress, hf] <;> rfl
  | wrongTy id c hp hf ht => rw [hp]; simp [cellAddress, hf, ht] <;> rfl
  | unsupported id c hp hf ht hs => rw [hp]; simp [cellAddress, hf, ht, hs] <;> rfl
  | ready id c r hp hf ht hs hr =>
    rw [hp]
    simp only [cellAddress, hf, ht, hs]
    change ofR (f c) = r
    exact h c r hr

theorem expectCell_bind (k : Core) (ptr : Val) (ty : Ty) (f : Cell → R Core) :
    (expectCell k ptr ty >>= f) =
      (rejectPoison ptr "private cell address" >>= fun _ => cellAddress k ptr ty >>= f) := by
  unfold expectCell
  cases rejectPoison ptr "private cell address" <;> rfl

theorem cellAccess_complete (k : Core) (ptr : Val) (ty : Ty)
    (P : Cell → StepR → Prop) (f : Cell → R Core) (h : ∀ c, P c (ofR (f c))) :
    Seq (rejectPoison ptr "private cell address") (fun _ => CellAddress k ptr ty P)
      (ofR (expectCell k ptr ty >>= f)) := by
  rw [expectCell_bind]
  exact seq_of_bind _ _ _ (fun _ => cellAddress_complete k ptr ty P f h)

theorem cellAccess_sound (k : Core) (ptr : Val) (ty : Ty)
    (P : Cell → StepR → Prop) (f : Cell → R Core)
    (h : ∀ c r, P c r → ofR (f c) = r) (r : StepR)
    (hc : Seq (rejectPoison ptr "private cell address") (fun _ => CellAddress k ptr ty P) r) :
    ofR (expectCell k ptr ty >>= f) = r := by
  rw [expectCell_bind]
  exact bind_of_seq _ _ _ _ (fun _ r hp => cellAddress_sound k ptr ty P f h r hp) hc

theorem selects_complete (k : Core) (node : Node) (tv ev cv : Val) :
    Selects k node.results tv ev cv (ofR (selectOn k node tv ev cv)) := by
  unfold selectOn
  cases hb : asBool cv with
  | none => exact Selects.notBool hb
  | some b =>
    cases b with
    | false => exact Selects.no hb _ (binds_complete _ _ _)
    | true => exact Selects.yes hb _ (binds_complete _ _ _)

theorem selects_sound (k : Core) (node : Node) (tv ev cv : Val) (r : StepR)
    (h : Selects k node.results tv ev cv r) : ofR (selectOn k node tv ev cv) = r := by
  unfold selectOn
  cases h with
  | yes hb r hr => rw [hb]; exact binds_sound _ _ _ _ hr
  | no hb r hr => rw [hb]; exact binds_sound _ _ _ _ hr
  | notBool hb => rw [hb]; rfl

theorem slotWrite_complete (k : Core) (node : Node) (l : Nat) (s : List (Option Val)) (slot : Nat)
    (v : Val) : SlotWrite k node.results l s slot v (ofR (bindSlotAt k node l s slot v)) := by
  unfold bindSlotAt
  by_cases h : s.length ≤ slot
  · rw [if_pos h]; exact SlotWrite.range h
  · rw [if_neg h]; exact SlotWrite.write h _ (binds_complete _ _ _)

theorem slotWrite_sound (k : Core) (node : Node) (l : Nat) (s : List (Option Val)) (slot : Nat)
    (v : Val) (r : StepR) (h : SlotWrite k node.results l s slot v r) :
    ofR (bindSlotAt k node l s slot v) = r := by
  unfold bindSlotAt
  cases h with
  | range h => rw [if_pos h]; rfl
  | write h r hb => rw [if_neg h]; exact binds_sound _ _ _ _ hb

theorem slotRead_complete (pointerBits : Nat) (k : Core) (node : Node) (slot : Nat) (ty : Ty) (s : List (Option Val)) :
    SlotRead pointerBits k node.results slot ty s (ofR (loadSlotAt pointerBits k node slot ty s)) := by
  unfold loadSlotAt
  cases hs : nth? s slot with
  | none => exact SlotRead.range hs
  | some bound =>
    cases bound with
    | some v => exact SlotRead.bound v _ hs (seq_of_bind _ _ _ (fun _ => binds_complete _ _ _))
    | none =>
      cases hsc : isScalarTy ty with
      | false => exact SlotRead.nonScalar hs hsc
      | true => exact SlotRead.poison hs hsc _ (binds_complete _ _ _)

theorem loadSlotAt_bound (pointerBits : Nat) (k : Core) (node : Node) (slot : Nat) (ty : Ty) (s : List (Option Val))
    (v : Val) (hs : nth? s slot = some (some v)) :
    loadSlotAt pointerBits k node slot ty s = (do expectTy pointerBits v ty; bindResults (next k) node [v]) := by
  unfold loadSlotAt
  rw [hs]

theorem slotRead_sound (pointerBits : Nat) (k : Core) (node : Node) (slot : Nat) (ty : Ty) (s : List (Option Val))
    (r : StepR) (h : SlotRead pointerBits k node.results slot ty s r) :
    ofR (loadSlotAt pointerBits k node slot ty s) = r := by
  cases h with
  | range hs => unfold loadSlotAt; rw [hs]; rfl
  | bound v r hs hq =>
    rw [loadSlotAt_bound pointerBits k node slot ty s v hs]
    cases hq with
    | ok u r1 hx h1 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h1
    | stop o hx => rw [hx]; rfl
  | poison hs hsc r hb => unfold loadSlotAt; rw [hs]; rw [hsc]; exact binds_sound _ _ _ _ hb
  | nonScalar hs hsc => unfold loadSlotAt; rw [hs]; rw [hsc]; rfl

theorem closes_complete (k : Core) (node : Node) (l : Nat) :
    Closes k node.results l (ofR (closeAt k node l)) := by
  unfold closeAt
  cases hm : memNat k.openFrames l
  · exact Closes.twice hm
  · exact Closes.close hm _ (binds_complete _ _ _)

theorem closes_sound (k : Core) (node : Node) (l : Nat) (r : StepR)
    (h : Closes k node.results l r) : ofR (closeAt k node l) = r := by
  unfold closeAt
  cases h with
  | close hm r hb => rw [hm]; exact binds_sound _ _ _ _ hb
  | twice hm => rw [hm]; rfl

theorem asserts_complete (k : Core) (kind : AssertKind) (cv : Val) :
    Asserts k kind cv (ofR (assertOn k kind cv)) := by
  unfold assertOn
  cases hb : asBool cv with
  | none => exact Asserts.notBool hb
  | some b =>
    cases b with
    | false => exact Asserts.fail hb _ (seq_of_bind _ _ _ (fun _ => rfl))
    | true => exact Asserts.pass hb

theorem asserts_sound (k : Core) (kind : AssertKind) (cv : Val) (r : StepR)
    (h : Asserts k kind cv r) : ofR (assertOn k kind cv) = r := by
  unfold assertOn
  cases h with
  | pass hb => rw [hb]; rfl
  | fail hb r hq => rw [hb]; exact bind_of_seq _ _ _ _ (fun msg r h => h.symm) hq
  | notBool hb => rw [hb]; rfl

theorem branches_complete (pointerBits : Nat) (k : Core) (tT : Nat) (tA : List Nat) (eT : Nat) (eA : List Nat)
    (cv : Val) : Branches pointerBits k tT tA eT eA cv (ofR (branchOn pointerBits k tT tA eT eA cv)) := by
  unfold branchOn
  cases hb : asBool cv with
  | none => exact Branches.notBool hb
  | some b =>
    cases b with
    | false => exact Branches.no hb _ (seq_of_bind _ _ _ (fun _ => jumps_complete pointerBits _ _ _))
    | true => exact Branches.yes hb _ (seq_of_bind _ _ _ (fun _ => jumps_complete pointerBits _ _ _))

theorem branches_sound (pointerBits : Nat) (k : Core) (tT : Nat) (tA : List Nat) (eT : Nat) (eA : List Nat)
    (cv : Val) (r : StepR) (h : Branches pointerBits k tT tA eT eA cv r) :
    ofR (branchOn pointerBits k tT tA eT eA cv) = r := by
  unfold branchOn
  cases h with
  | yes hb r hq => rw [hb]; exact bind_of_seq _ _ _ _ (fun vs r h => jumps_sound pointerBits _ _ _ _ h) hq
  | no hb r hq => rw [hb]; exact bind_of_seq _ _ _ _ (fun vs r h => jumps_sound pointerBits _ _ _ _ h) hq
  | notBool hb => rw [hb]; rfl

theorem picks_complete (pointerBits : Nat) (k : Core) (dflt : Nat) (dArgs : List Nat) (o : Option (Nat × List Nat)) :
    Picks pointerBits k dflt dArgs o (ofR (pickOn pointerBits k dflt dArgs o)) := by
  cases o with
  | none =>
    exact Picks.dflt (ofR (pickOn pointerBits k dflt dArgs none))
      (seq_of_bind _ _ _ (fun _ => jumps_complete pointerBits _ _ _))
  | some p =>
    cases p with
    | mk t as => exact Picks.case t as _ (seq_of_bind _ _ _ (fun _ => jumps_complete pointerBits _ _ _))

theorem picks_sound (pointerBits : Nat) (k : Core) (dflt : Nat) (dArgs : List Nat) (o : Option (Nat × List Nat))
    (r : StepR) (h : Picks pointerBits k dflt dArgs o r) : ofR (pickOn pointerBits k dflt dArgs o) = r := by
  cases h with
  | case t as r hq => exact bind_of_seq _ _ _ _ (fun vs r h => jumps_sound pointerBits _ _ _ _ h) hq
  | dflt r hq => exact bind_of_seq _ _ _ _ (fun vs r h => jumps_sound pointerBits _ _ _ _ h) hq

theorem switches_complete (m : Module) (k : Core) (dflt : Nat) (dArgs : List Nat)
    (cases : List (Const × Nat × List Nat)) (v : Val) :
    Switches m k dflt dArgs cases v (ofR (switchOn m k dflt dArgs cases v)) := by
  unfold switchOn
  cases hv : switchable v with
  | false => exact Switches.other hv
  | true =>
    exact Switches.scalar hv _ (seq_of_bind _ _ _ (fun o => picks_complete m.pointerBits _ _ _ o))

theorem switches_sound (m : Module) (k : Core) (dflt : Nat) (dArgs : List Nat)
    (cases : List (Const × Nat × List Nat)) (v : Val) (r : StepR)
    (h : Switches m k dflt dArgs cases v r) : ofR (switchOn m k dflt dArgs cases v) = r := by
  unfold switchOn
  cases h with
  | scalar hv r hq =>
    rw [hv]
    exact bind_of_seq _ _ _ _ (fun o r h => picks_sound m.pointerBits _ _ _ _ _ h) hq
  | other hv => rw [hv]; rfl

theorem enters_complete (pointerBits : Nat) (k : Core) (node : Node) (f : Func) (sig : FuncTy) (vs : List Val) :
    Enters pointerBits k node f sig vs (ofR (enterFn pointerBits k node f sig vs)) := by
  unfold enterFn
  cases he : f.blocks.isEmpty
  · cases hb : findBlock f.blocks f.entry with
    | none => exact Enters.noEntry he hb
    | some b => exact Enters.push b _ he hb (paramsBind_complete pointerBits _ _ _ _ _ (fun _ => rfl))
  · exact Enters.decl he

theorem enters_sound (pointerBits : Nat) (k : Core) (node : Node) (f : Func) (sig : FuncTy) (vs : List Val) (r : StepR)
    (h : Enters pointerBits k node f sig vs r) : ofR (enterFn pointerBits k node f sig vs) = r := by
  unfold enterFn
  cases h with
  | decl he => rw [he]; rfl
  | noEntry he hb => rw [he]; rw [hb]; rfl
  | push b r he hb hq =>
    rw [he]; rw [hb]
    exact paramsBind_sound pointerBits _ _ (fun _ r h => h.symm) _ _ _ _ hq

theorem callSigned_complete (m : Module) (k : Core) (node : Node) (callee : Nat) (vs : List Val)
    (f : Func) (sig : FuncTy) (hd : (k.depth == 0) = false)
    (hf : m.functions.find? (fun f => f.id == callee) = some f) (hsig : nth? m.funcTys f.ty = some sig) :
    Calls m k node callee vs (ofR (callSigned m.pointerBits k node f sig vs)) := by
  unfold callSigned
  cases hv : sig.vararg
  · exact Calls.enter f sig _ hd hf hsig hv
      (sigChecks_complete m.pointerBits _ _ _ _ (fun _ => enters_complete m.pointerBits _ _ _ _ _))
  · cases he : f.blocks.isEmpty
    · exact Calls.varargDef f sig hd hf hsig hv he
    · exact Calls.varargDecl f sig hd hf hsig hv he

theorem callSig_complete (m : Module) (k : Core) (node : Node) (callee : Nat) (vs : List Val)
    (f : Func) (hd : (k.depth == 0) = false)
    (hf : m.functions.find? (fun f => f.id == callee) = some f) (o : Option FuncTy)
    (ho : nth? m.funcTys f.ty = o) : Calls m k node callee vs (ofR (callSig m.pointerBits k node f vs o)) := by
  cases o with
  | none => exact Calls.noSig f hd hf ho
  | some sig => exact callSigned_complete m k node callee vs f sig hd hf ho

theorem calls_complete (m : Module) (k : Core) (node : Node) (callee : Nat) (vs : List Val) :
    Calls m k node callee vs (ofR (callOn m k node callee vs)) := by
  unfold callOn
  cases hd : (k.depth == 0)
  · cases hf : m.functions.find? (fun f => f.id == callee) with
    | none => exact Calls.noFn hd hf
    | some f => exact callSig_complete m k node callee vs f hd hf (nth? m.funcTys f.ty) rfl
  · exact Calls.depth hd

theorem callFn_some (m : Module) (k : Core) (node : Node) (vs : List Val) (f : Func) :
    callFn m k node vs (some f) = callSig m.pointerBits k node f vs (nth? m.funcTys f.ty) := rfl

theorem callSig_some (pointerBits : Nat) (k : Core) (node : Node) (f : Func) (vs : List Val) (sig : FuncTy) :
    callSig pointerBits k node f vs (some sig) = callSigned pointerBits k node f sig vs := rfl

theorem calls_sound (m : Module) (k : Core) (node : Node) (callee : Nat) (vs : List Val) (r : StepR)
    (h : Calls m k node callee vs r) : ofR (callOn m k node callee vs) = r := by
  unfold callOn
  cases h with
  | depth hd => rw [hd]; rfl
  | noFn hd hf => rw [hd]; rw [hf]; rfl
  | noSig f hd hf hsig => rw [hd]; rw [hf]; rw [callFn_some]; rw [hsig]; rfl
  | varargDecl f sig hd hf hsig hv he =>
    rw [hd]; rw [hf]; rw [callFn_some]; rw [hsig]; rw [callSig_some]
    unfold callSigned
    rw [hv]; rw [he]; rfl
  | varargDef f sig hd hf hsig hv he =>
    rw [hd]; rw [hf]; rw [callFn_some]; rw [hsig]; rw [callSig_some]
    unfold callSigned
    rw [hv]; rw [he]; rfl
  | enter f sig r hd hf hsig hv hq =>
    rw [hd]; rw [hf]; rw [callFn_some]; rw [hsig]; rw [callSig_some]
    unfold callSigned
    rw [hv]
    exact sigChecks_sound m.pointerBits _ _ (fun _ r h => enters_sound m.pointerBits _ _ _ _ _ _ h) _ _ _ hq

theorem returns_complete (k : Core) (vs : List Val) : Returns k vs (ofR (returnTo k vs)) := by
  unfold returnTo
  cases hst : k.stack with
  | nil => exact Returns.top hst
  | cons c rest => exact Returns.pop c rest _ hst (binds_complete _ c.node vs)

theorem returns_sound (k : Core) (vs : List Val) (r : StepR) (h : Returns k vs r) :
    ofR (returnTo k vs) = r := by
  unfold returnTo
  cases h with
  | top hst => rw [hst]; rfl
  | pop c rest r hst hb => rw [hst]; exact binds_sound _ _ _ _ hb

theorem accessAt_some (m : Mem) (op : String) (a o size align : Nat) (al : Alloc)
    (hn : nth? m.allocs a = some al) :
    accessAt m op a o size align = accessAlloc op al o size align := by
  unfold accessAt
  rw [hn]

theorem accesses_complete (m : Mem) (op : String) (a o size align : Nat)
    (P : Alloc → StepR → Prop) (f : Alloc → R Core) (h : ∀ al, P al (ofR (f al))) :
    Accesses m op a o size align P (ofR (accessAt m op a o size align >>= f)) := by
  cases hn : nth? m.allocs a with
  | none => unfold accessAt; rw [hn]; exact Accesses.unknown hn
  | some al =>
    rw [accessAt_some m op a o size align al hn]
    unfold accessAlloc
    cases hl : al.live with
    | false => exact Accesses.dead al hn hl
    | true =>
      cases h1 : decide (addrSpace ≤ al.base + o) with
      | true => exact Accesses.addrOverflow al hn hl h1
      | false =>
        cases h2 : ((al.base + o) % align != 0) with
        | true => exact Accesses.misaligned al hn hl h1 h2
        | false =>
          cases h3 : decide (addrSpace ≤ o + size) with
          | true => exact Accesses.rangeOverflow al hn hl h1 h2 h3
          | false =>
            cases h4 : decide (al.size < o + size) with
            | true => exact Accesses.outOfBounds al hn hl h1 h2 h3 h4
            | false => exact Accesses.ok al _ hn hl h1 h2 h3 h4 (h al)

theorem accesses_sound (m : Mem) (op : String) (a o size align : Nat)
    (P : Alloc → StepR → Prop) (f : Alloc → R Core) (h : ∀ al r, P al r → ofR (f al) = r)
    (r : StepR) (hs : Accesses m op a o size align P r) :
    ofR (accessAt m op a o size align >>= f) = r := by
  cases hs with
  | unknown hn => unfold accessAt; rw [hn]; rfl
  | dead al hn hl =>
    rw [accessAt_some m op a o size align al hn]; unfold accessAlloc; rw [hl]; rfl
  | addrOverflow al hn hl h1 =>
    rw [accessAt_some m op a o size align al hn]; unfold accessAlloc; rw [hl, h1]; rfl
  | misaligned al hn hl h1 h2 =>
    rw [accessAt_some m op a o size align al hn]; unfold accessAlloc; rw [hl, h1, h2]; rfl
  | rangeOverflow al hn hl h1 h2 h3 =>
    rw [accessAt_some m op a o size align al hn]; unfold accessAlloc; rw [hl, h1, h2, h3]; rfl
  | outOfBounds al hn hl h1 h2 h3 h4 =>
    rw [accessAt_some m op a o size align al hn]; unfold accessAlloc; rw [hl, h1, h2, h3, h4]; rfl
  | ok al r hn hl h1 h2 h3 h4 hp =>
    rw [accessAt_some m op a o size align al hn]; unfold accessAlloc; rw [hl, h1, h2, h3, h4]
    exact h al r hp

theorem reads_complete (k : Core) (node : Node) (ty : Ty) (vol : Bool) (o : Nat) (bs : List AByte) :
    Reads k node.results ty vol o bs (ofR (readOut k node ty vol o bs)) := by
  unfold readOut
  cases hf : firstUninit bs with
  | none => exact Reads.init hf _ (seq_of_bind _ _ _ (fun _ => binds_complete _ _ _))
  | some i =>
    cases vol with
    | true => exact Reads.strict i hf rfl
    | false => exact Reads.poison i _ hf rfl (binds_complete _ _ _)

theorem reads_sound (k : Core) (node : Node) (ty : Ty) (vol : Bool) (o : Nat) (bs : List AByte)
    (r : StepR) (h : Reads k node.results ty vol o bs r) :
    ofR (readOut k node ty vol o bs) = r := by
  unfold readOut
  cases h with
  | init hf r hs =>
    rw [hf]
    exact bind_of_seq (decodeVal ty bs) (fun v => bindResults (next k) node [v])
      (fun v => Binds (next k) node.results [v]) r
      (fun (v : Val) (r : StepR) (h : Binds (next k) node.results [v] r) => binds_sound _ _ _ _ h) hs
  | strict i hf hv => rw [hf, hv]; rfl
  | poison i r hf hv hb => rw [hf, hv]; exact binds_sound _ _ _ _ hb

theorem allocates_complete (pointerBits : Nat) (k : Core) (node : Node) (size align : Nat) :
    Allocates pointerBits k node.results size align (ofR (allocAt pointerBits k node size align)) := by
  unfold allocAt
  cases h1 : decide (addrSpace ≤ k.mem.nextAddr + (align - 1)) with
  | true => exact Allocates.oomAlign h1
  | false =>
    cases h2 : decide (addrSpace ≤ alignUp k.mem.nextAddr align + max size 1) with
    | true => exact Allocates.oomEnd h1 h2
    | false =>
      cases ht : decide (2 ^ pointerBits < alignUp k.mem.nextAddr align + max size 1) with
      | true => exact Allocates.oomTarget h1 h2 ht
      | false => exact Allocates.fresh h1 h2 ht _ (binds_complete _ _ _)

theorem allocates_sound (pointerBits : Nat) (k : Core) (node : Node) (size align : Nat) (r : StepR)
    (h : Allocates pointerBits k node.results size align r) : ofR (allocAt pointerBits k node size align) = r := by
  unfold allocAt
  cases h with
  | oomAlign h1 => rw [h1]; rfl
  | oomEnd h1 h2 => rw [h1, h2]; rfl
  | oomTarget h1 h2 ht => rw [h1, h2, ht]; rfl
  | fresh h1 h2 ht r hb => rw [h1, h2, ht]; exact binds_sound _ _ _ _ hb

theorem freeAt_some (k : Core) (node : Node) (a o : Nat) (al : Alloc) (h0 : (o != 0) = false)
    (hn : nth? k.mem.allocs a = some al) : freeAt k node a o = freeAlloc k node a al := by
  unfold freeAt
  rw [h0, hn]

theorem frees_complete (k : Core) (node : Node) (a o : Nat) :
    Frees k node.results a o (ofR (freeAt k node a o)) := by
  cases h0 : (o != 0) with
  | true => unfold freeAt; rw [h0]; exact Frees.interior h0
  | false =>
    cases hn : nth? k.mem.allocs a with
    | none => unfold freeAt; rw [h0, hn]; exact Frees.unknown h0 hn
    | some al =>
      rw [freeAt_some k node a o al h0 hn]
      unfold freeAlloc
      cases hl : al.live with
      | false => exact Frees.dead al h0 hn hl
      | true => exact Frees.free al _ h0 hn hl (binds_complete _ _ _)

theorem frees_sound (k : Core) (node : Node) (a o : Nat) (r : StepR)
    (h : Frees k node.results a o r) : ofR (freeAt k node a o) = r := by
  cases h with
  | interior h0 => unfold freeAt; rw [h0]; rfl
  | unknown h0 hn => unfold freeAt; rw [h0, hn]; rfl
  | dead al h0 hn hl => rw [freeAt_some k node a o al h0 hn]; unfold freeAlloc; rw [hl]; rfl
  | free al r h0 hn hl hb =>
    rw [freeAt_some k node a o al h0 hn]; unfold freeAlloc; rw [hl]
    exact binds_sound _ _ _ _ hb

theorem offsets_complete (pointerBits : Nat) (k : Core) (node : Node) (a o d : Nat) :
    Offsets pointerBits k node.results a o d (ofR (gepAt pointerBits k node a o d)) := by
  unfold gepAt
  cases h : decide (addrSpace ≤ o + d) with
  | true => exact Offsets.overflow h
  | false =>
    cases hw : (pointerBits != 64) with
    | false => exact Offsets.wide h hw _ (binds_complete _ _ _)
    | true =>
      cases hn : nth? k.mem.allocs a with
      | none => exact Offsets.unknown h hw hn
      | some al =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hb : (decide (addrSpace ≤ al.base + o) || decide (2 ^ pointerBits ≤ al.base + o)) with
        | true => exact Offsets.baseOverflow al h hw hn hb
        | false =>
          cases hu : decide (addrSpace ≤ al.base + o + d) with
          | true => exact Offsets.addressOverflow al h hw hn hb hu
          | false =>
            cases ht : decide (2 ^ pointerBits ≤ al.base + o + d) with
            | true => exact Offsets.outside al h hw hn hb hu ht
            | false => exact Offsets.ok al h hw hn hb hu ht _ (binds_complete _ _ _)

theorem offsets_sound (pointerBits : Nat) (k : Core) (node : Node) (a o d : Nat) (r : StepR)
    (h : Offsets pointerBits k node.results a o d r) : ofR (gepAt pointerBits k node a o d) = r := by
  unfold gepAt
  cases h with
  | overflow h => rw [h]; rfl
  | wide h hw r hb => rw [h, hw]; exact binds_sound _ _ _ _ hb
  | unknown h hw hn => rw [h, hw, hn]; rfl
  | baseOverflow al h hw hn hb => simp only [h, hw, hn, ↓reduceIte]; rw [hb]; rfl
  | addressOverflow al h hw hn hb hu => simp only [h, hw, hn, ↓reduceIte]; rw [hb, hu]; rfl
  | outside al h hw hn hb hu ht => simp only [h, hw, hn, ↓reduceIte]; rw [hb, hu, ht]; rfl
  | ok al h hw hn hb hu ht r hr =>
    simp only [h, hw, hn, ↓reduceIte]; rw [hb, hu, ht]; exact binds_sound _ _ _ _ hr

/-! Each instruction's step function satisfies only its rule: the soundness
    half, instruction by instruction. -/

theorem binop_sound (pointerBits : Nat) (k : Core) (node : Node) (op : BinOp) (ty : Ty) (l r : Nat) (res : StepR)
    (hs : Seq (getV k l) (fun a =>
        Seq (getV k r) (fun b =>
        Seq (evalBinop pointerBits op ty a b) (fun v =>
        Binds (next k) node.results [v]))) res) :
    ofR (binopStep pointerBits k node op ty l r) = res := by
  unfold binopStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok b r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok v r3 hx h3 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h3

theorem unop_sound (pointerBits : Nat) (k : Core) (node : Node) (op : UnOp) (ty : Ty) (x : Nat) (res : StepR)
    (hs : Seq (getV k x) (fun a =>
        Seq (evalUnop pointerBits op ty a) (fun v =>
        Binds (next k) node.results [v])) res) :
    ofR (unopStep pointerBits k node op ty x) = res := by
  unfold unopStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok v r2 hx h2 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h2

theorem overflow_sound (pointerBits : Nat) (k : Core) (node : Node) (op : OvfOp) (ty : Ty) (l r : Nat) (res : StepR)
    (hs : Seq (getV k l) (fun a =>
        Seq (getV k r) (fun b =>
        Seq (evalOverflow pointerBits op ty a b) (fun vs =>
        Binds (next k) node.results vs))) res) :
    ofR (overflowStep pointerBits k node op ty l r) = res := by
  unfold overflowStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok b r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok vs r3 hx h3 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h3

theorem icmp_sound (pointerBits : Nat) (k : Core) (node : Node) (op : ICmpOp) (ty : Ty) (l r : Nat) (res : StepR)
    (hs : Seq (getV k l) (fun a =>
        Seq (getV k r) (fun b =>
        Seq (evalIcmp pointerBits op ty a b) (fun v =>
        Binds (next k) node.results [v]))) res) :
    ofR (icmpStep pointerBits k node op ty l r) = res := by
  unfold icmpStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok b r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok v r3 hx h3 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h3

theorem const_sound (m : Module) (k : Core) (node : Node) (ty : Ty) (c : Const) (res : StepR)
    (hs : Seq (constVal m 8 ty c) (fun v =>
        Binds (next k) node.results [v]) res) :
    ofR (constStep m k node ty c) = res := by
  unfold constStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok v r1 hx h1 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h1

theorem copy_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (x : Nat) (res : StepR)
    (hs : Seq (getV k x) (fun a =>
        Seq (expectTy pointerBits a ty) (fun _ =>
        Binds (next k) node.results [a])) res) :
    ofR (copyStep pointerBits k node ty x) = res := by
  unfold copyStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok u r2 hx h2 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h2

theorem select_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (c t e : Nat) (res : StepR)
    (hs : Seq (getV k c) (fun cv =>
        Seq (getV k t) (fun tv =>
        Seq (getV k e) (fun ev =>
        Seq (rejectPoison cv "select") (fun _ =>
        Seq (expectTy pointerBits tv ty) (fun _ =>
        Seq (expectTy pointerBits ev ty) (fun _ =>
        Selects k node.results tv ev cv)))))) res) :
    ofR (selectStep pointerBits k node ty c t e) = res := by
  unfold selectStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok cv r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok tv r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok ev r3 hx h3 =>
        rw [hx, ok_bind]
        cases h3 with
        | stop o hx => rw [hx]; rfl
        | ok u1 r4 hx h4 =>
          rw [hx, ok_bind]
          cases h4 with
          | stop o hx => rw [hx]; rfl
          | ok u2 r5 hx h5 =>
            rw [hx, ok_bind]
            cases h5 with
            | stop o hx => rw [hx]; rfl
            | ok u3 r6 hx h6 => rw [hx, ok_bind]; exact selects_sound _ _ _ _ _ _ h6

theorem extractField_sound (m : Module) (k : Core) (node : Node) (ty : Ty) (agg field : Nat) (res : StepR)
    (hs : Seq (getV k agg) (fun a =>
        Seq (evalExtract m ty a field) (fun v =>
        Binds (next k) node.results [v])) res) :
    ofR (extractFieldStep m k node ty agg field) = res := by
  unfold extractFieldStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok v r2 hx h2 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h2

theorem insertField_sound (m : Module) (k : Core) (node : Node) (ty : Ty) (agg field x : Nat) (res : StepR)
    (hs : Seq (getV k agg) (fun a =>
        Seq (getV k x) (fun v =>
        Seq (evalInsert m ty a field v) (fun w =>
        Binds (next k) node.results [w]))) res) :
    ofR (insertFieldStep m k node ty agg field x) = res := by
  unfold insertFieldStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok v r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok w r3 hx h3 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h3

theorem bindSlot_sound (k : Core) (node : Node) (f slot x : Nat) (res : StepR)
    (hs : Seq (getV k f) (fun h =>
        Seq (expectFrame h) (fun ls =>
        Opened k "BindSlot" ls.1 (Seq (getV k x) (fun v =>
        SlotWrite k node.results ls.1 ls.2 slot v)))) res) :
    ofR (bindSlotStep k node f slot x) = res := by
  unfold bindSlotStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok h r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok ls r2 hx h2 =>
      rw [hx, ok_bind]
      exact opened_sound _ _ _ _ _ _
        (fun r h3 => bind_of_seq _ _ _ _ (fun v r h4 => slotWrite_sound _ _ _ _ _ _ _ h4) h3) h2

theorem loadSlot_sound (pointerBits : Nat) (k : Core) (node : Node) (f slot : Nat) (ty : Ty) (res : StepR)
    (hs : Seq (getV k f) (fun h =>
        Seq (expectFrame h) (fun ls =>
        Opened k "LoadSlot" ls.1 (SlotRead pointerBits k node.results slot ty ls.2))) res) :
    ofR (loadSlotStep pointerBits k node f slot ty) = res := by
  unfold loadSlotStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok h r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok ls r2 hx h2 =>
      rw [hx, ok_bind]
      exact opened_sound _ _ _ _ _ _ (fun r h3 => slotRead_sound pointerBits _ _ _ _ _ _ h3) h2

theorem closeFrame_sound (k : Core) (node : Node) (f : Nat) (res : StepR)
    (hs : Seq (getV k f) (fun v =>
        Seq (expectFrame v) (fun ls =>
        Closes k node.results ls.1)) res) :
    ofR (closeFrameStep k node f) = res := by
  unfold closeFrameStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok v r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok ls r2 hx h2 => rw [hx, ok_bind]; exact closes_sound _ _ _ _ h2

theorem assert_sound (k : Core) (node : Node) (c : Nat) (kind : AssertKind) (res : StepR)
    (hs : Seq (getV k c) (fun cv =>
        Seq (rejectPoison cv "assert") (fun _ =>
        Asserts k kind cv)) res) :
    ofR (assertStep k node c kind) = res := by
  unfold assertStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok cv r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok u r2 hx h2 => rw [hx, ok_bind]; exact asserts_sound _ _ _ _ h2

theorem call_sound (m : Module) (k : Core) (node : Node) (callee : Nat) (args : List Nat) (res : StepR)
    (hs : Seq (getVs k args) (fun vs =>
        Calls m k node callee vs) res) :
    ofR (callStep m k node callee args) = res := by
  unfold callStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok vs r1 hx h1 => rw [hx, ok_bind]; exact calls_sound _ _ _ _ _ _ h1

theorem makesClosure_complete (m : Module) (k : Core) (node : Node) (cid target : Nat)
    (captures : List Val) :
    MakesClosure m k node.results cid target captures
      (ofR (makeClosureOn m k node cid target captures)) := by
  unfold makeClosureOn
  cases hc : nth? m.closures cid with
  | none => exact MakesClosure.noClosure hc
  | some c =>
    simp only
    cases ha : nth? m.funcTys c.func with
    | none => exact MakesClosure.noApparent c hc ha
    | some apparent =>
      simp only
      cases hf : m.functions.find? (fun f => f.id == target) with
      | none => exact MakesClosure.noFunction c apparent hc ha hf
      | some f =>
        simp only
        cases hp : nth? m.funcTys f.ty with
        | none => exact MakesClosure.noPhysical c apparent f hc ha hf hp
        | some physical =>
          simp only
          cases hb : (apparent.vararg || physical.vararg ||
            !(tyListEq physical.params (c.captures ++ apparent.params)) ||
            !(tyListEq physical.returns apparent.returns)) with
          | true => exact MakesClosure.mismatch c apparent f physical hc ha hf hp hb
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact MakesClosure.checked c apparent f physical _ hc ha hf hp hb
              (sigChecks_complete m.pointerBits _ _ captures c.captures
                (fun _ => binds_complete (next k) node [.closure cid target captures]))

theorem makesClosure_sound (m : Module) (k : Core) (node : Node) (cid target : Nat)
    (captures : List Val) (r : StepR)
    (h : MakesClosure m k node.results cid target captures r) :
    ofR (makeClosureOn m k node cid target captures) = r := by
  unfold makeClosureOn
  cases h with
  | noClosure hc => simp only [hc]; rfl
  | noApparent c hc ha => simp only [hc, ha]; rfl
  | noFunction c apparent hc ha hf => simp only [hc, ha, hf]; rfl
  | noPhysical c apparent f hc ha hf hp => simp only [hc, ha, hf, hp]; rfl
  | mismatch c apparent f physical hc ha hf hp hb => simp only [hc, ha, hf, hp, hb]; rfl
  | checked c apparent f physical r hc ha hf hp hb hs =>
    simp only [hc, ha, hf, hp, hb, Bool.false_eq_true, ↓reduceIte]
    exact sigChecks_sound m.pointerBits _ _
      (fun _ r h => binds_sound (next k) node [.closure cid target captures] r h)
      captures c.captures r hs

theorem makeClosure_sound (m : Module) (k : Core) (node : Node) (cid target : Nat)
    (captures : List Nat) (r : StepR)
    (h : Seq (getVs k captures) (fun vs => MakesClosure m k node.results cid target vs) r) :
    ofR (makeClosureStep m k node cid target captures) = r := by
  unfold makeClosureStep
  cases h with
  | stop o hx => rw [hx]; rfl
  | ok vs r hx hs => rw [hx, ok_bind]; exact makesClosure_sound _ _ _ _ _ _ _ hs

theorem br_sound (pointerBits : Nat) (k : Core) (node : Node) (target : Nat) (args : List Nat) (res : StepR)
    (hs : Seq (getVs k args) (fun vs =>
        Jumps pointerBits k target vs) res) :
    ofR (brStep pointerBits k node target args) = res := by
  unfold brStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok vs r1 hx h1 => rw [hx, ok_bind]; exact jumps_sound pointerBits _ _ _ _ h1

theorem condBr_sound (pointerBits : Nat) (k : Core) (node : Node) (c tT : Nat) (tA : List Nat) (eT : Nat) (eA : List Nat) (res : StepR)
    (hs : Seq (getV k c) (fun cv =>
        Seq (rejectPoison cv "cond_br") (fun _ =>
        Branches pointerBits k tT tA eT eA cv)) res) :
    ofR (condBrStep pointerBits k node c tT tA eT eA) = res := by
  unfold condBrStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok cv r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok u r2 hx h2 => rw [hx, ok_bind]; exact branches_sound pointerBits _ _ _ _ _ _ _ h2

theorem cast_sound (pointerBits : Nat) (k : Core) (node : Node) (op : CastOp) (src dst : Ty) (x : Nat) (res : StepR)
    (hs : Seq (getV k x) (fun a =>
        Seq (evalCast pointerBits op src dst a) (fun v =>
        Binds (next k) node.results [v])) res) :
    ofR (castStep pointerBits k node op src dst x) = res := by
  unfold castStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok v r2 hx h2 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h2

theorem switch_sound (m : Module) (k : Core) (node : Node) (x dflt : Nat) (dArgs : List Nat)
    (cases : List (Const × Nat × List Nat)) (res : StepR)
    (hs : Seq (getV k x) (fun v =>
        Seq (rejectPoison v "switch") (fun _ =>
        Switches m k dflt dArgs cases v)) res) :
    ofR (switchStep m k node x dflt dArgs cases) = res := by
  unfold switchStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok v r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok u r2 hx h2 => rw [hx, ok_bind]; exact switches_sound _ _ _ _ _ _ _ h2

theorem ret_sound (pointerBits : Nat) (k : Core) (node : Node) (xs : List Nat) (res : StepR)
    (hs : Seq (getVs k xs) (fun vs =>
        SigChecks pointerBits (Returns k vs) vs k.sig.returns) res) :
    ofR (retStep pointerBits k node xs) = res := by
  unfold retStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok vs r1 hx h1 =>
    rw [hx, ok_bind]
    exact sigChecks_sound pointerBits _ _ (fun _ r h => returns_sound _ _ _ h) _ _ _ h1

theorem alloca_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (count al : Option Nat) (res : StepR)
    (hs : Seq (getCount k count) (fun cv => Seq (layoutOf pointerBits ty) (fun l => Seq (allocSize pointerBits l.1 cv)
        (fun size => Seq (checkAlign (al.getD l.2)) (fun align =>
          Allocates pointerBits k node.results size align)))) res) :
    ofR (allocaStep pointerBits k node ty count al) = res := by
  unfold allocaStep
  exact bind_of_seq _ _ _ _ (fun cv r1 h1 => bind_of_seq _ _ _ _ (fun l r2 h2 =>
    bind_of_seq _ _ _ _ (fun size r3 h3 => bind_of_seq _ _ _ _ (fun align r4 h4 =>
      allocates_sound pointerBits _ _ _ _ _ h4) h3) h2) h1) hs

theorem load_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (p : Nat) (vol : Bool) (al : Option Nat)
    (res : StepR)
    (hs : Seq (getV k p) (fun pv => Seq (scalarLayout pointerBits ty) (fun size => Seq (checkAlign (al.getD size))
        (fun align => Seq (expectPtr pv "Load") (fun ao =>
          Accesses k.mem "Load" ao.1 ao.2 size align (fun a =>
            Reads k node.results ty vol ao.2 (readBytes a.data ao.2 size)))))) res) :
    ofR (loadStep pointerBits k node ty p vol al) = res := by
  unfold loadStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok pv r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok size r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok align r3 hx h3 =>
        rw [hx, ok_bind]
        cases h3 with
        | stop o hx => rw [hx]; rfl
        | ok ao r4 hx h4 =>
          rw [hx, ok_bind]
          exact accesses_sound k.mem "Load" ao.1 ao.2 size align
            (fun a => Reads k node.results ty vol ao.2 (readBytes a.data ao.2 size))
            (fun a => readOut k node ty vol ao.2 (readBytes a.data ao.2 size))
            (fun (a : Alloc) (r : StepR) h => reads_sound _ _ _ _ _ _ _ h) _ h4

theorem store_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (p x : Nat) (vol : Bool) (al : Option Nat)
    (res : StepR)
    (hs : Seq (getV k p) (fun pv => Seq (getV k x) (fun v => Seq (scalarLayout pointerBits ty) (fun size =>
        Seq (storeImage pointerBits ty vol size v) (fun bs => Seq (checkAlign (al.getD size)) (fun align =>
          Seq (expectPtr pv "Store") (fun ao =>
            Accesses k.mem "Store" ao.1 ao.2 size align (fun a =>
              Binds { next k with
                      mem := { k.mem with
                               allocs := setNth k.mem.allocs ao.1
                                 { a with data := writeBytes a.data ao.2 bs } } }
                node.results []))))))) res) :
    ofR (storeStep pointerBits k node ty p x vol al) = res := by
  unfold storeStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok pv r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok v r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok size r3 hx h3 =>
        rw [hx, ok_bind]
        cases h3 with
        | stop o hx => rw [hx]; rfl
        | ok bs r4 hx h4 =>
          rw [hx, ok_bind]
          cases h4 with
          | stop o hx => rw [hx]; rfl
          | ok align r5 hx h5 =>
            rw [hx, ok_bind]
            cases h5 with
            | stop o hx => rw [hx]; rfl
            | ok ao r6 hx h6 =>
              rw [hx, ok_bind]
              exact accesses_sound k.mem "Store" ao.1 ao.2 size align
                (fun a => Binds { next k with
                                  mem := { k.mem with
                                           allocs := setNth k.mem.allocs ao.1
                                             { a with data := writeBytes a.data ao.2 bs } } }
                  node.results [])
                (fun a => bindResults { next k with mem := written k.mem ao.1 ao.2 a bs } node [])
                (fun (a : Alloc) (r : StepR) h => binds_sound _ _ _ _ h) _ h6

theorem gep_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (b : Nat) (idx : List Nat) (res : StepR)
    (hs : Seq (getV k b) (fun bv => Seq (getVs k idx) (fun ivs => Seq (layoutOf pointerBits ty) (fun l =>
        Seq (gepDelta pointerBits l.1 ivs 0) (fun d => Seq (expectPtr bv "GEP") (fun ao =>
          Offsets pointerBits k node.results ao.1 ao.2 d))))) res) :
    ofR (gepStep pointerBits k node ty b idx) = res := by
  unfold gepStep
  exact bind_of_seq _ _ _ _ (fun bv r1 h1 => bind_of_seq _ _ _ _ (fun ivs r2 h2 =>
    bind_of_seq _ _ _ _ (fun l r3 h3 => bind_of_seq _ _ _ _ (fun d r4 h4 =>
      bind_of_seq _ _ _ _ (fun ao r5 h5 => offsets_sound pointerBits _ _ _ _ _ _ h5) h4) h3) h2) h1) hs

theorem dealloc_sound (k : Core) (node : Node) (p : Nat) (res : StepR)
    (hs : Seq (getV k p) (fun pv => Seq (expectPtr pv "Dealloc") (fun ao =>
        Frees k node.results ao.1 ao.2)) res) :
    ofR (deallocStep k node p) = res := by
  unfold deallocStep
  exact bind_of_seq _ _ _ _ (fun pv r1 h1 => bind_of_seq _ _ _ _ (fun ao r2 h2 =>
    frees_sound _ _ _ _ _ h2) h1) hs

theorem tensorContract_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (l r : Nat)
    (batch contract : List (Nat × Nat)) (res : StepR)
    (hs : Seq (getV k l) (fun a =>
        Seq (getV k r) (fun b =>
        Seq (evalContract pointerBits ty batch contract a b) (fun v =>
        Binds (next k) node.results [v]))) res) :
    ofR (tensorContractStep pointerBits k node ty l r batch contract) = res := by
  unfold tensorContractStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok b r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok v r3 hx h3 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h3

theorem tensorMap_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (args : List Nat)
    (body : List MapNode) (res : StepR)
    (hs : Seq (getVs k args) (fun vs =>
        Seq (evalMap pointerBits ty vs body) (fun v =>
        Binds (next k) node.results [v])) res) :
    ofR (tensorMapStep pointerBits k node ty args body) = res := by
  unfold tensorMapStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok vs r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok v r2 hx h2 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h2

theorem tensorReduce_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (src : Nat)
    (op : ReduceOp) (axes : List Nat) (res : StepR)
    (hs : Seq (getV k src) (fun a =>
        Seq (evalReduce pointerBits ty op axes a) (fun v =>
        Binds (next k) node.results [v])) res) :
    ofR (tensorReduceStep pointerBits k node ty src op axes) = res := by
  unfold tensorReduceStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok v r2 hx h2 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h2

theorem tensorView_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (src : Nat)
    (params : List Nat) (exprs : List IxExpr) (shape index : List Nat) (fill : Option Nat)
    (res : StepR)
    (hs : Seq (getV k src) (fun a =>
        Seq (getVs k params) (fun ps =>
        Seq (getOptV k fill) (fun f =>
        Seq (evalView pointerBits ty a ps exprs shape index f) (fun v =>
        Binds (next k) node.results [v])))) res) :
    ofR (tensorViewStep pointerBits k node ty src params exprs shape index fill) = res := by
  unfold tensorViewStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok ps r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok f r3 hx h3 =>
        rw [hx, ok_bind]
        cases h3 with
        | stop o hx => rw [hx]; rfl
        | ok v r4 hx h4 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h4

theorem tensorGather_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty) (data : Nat)
    (coords : List Nat) (res : StepR)
    (hs : Seq (getV k data) (fun d =>
        Seq (getVs k coords) (fun cs =>
        Seq (evalGather pointerBits ty d cs) (fun v =>
        Binds (next k) node.results [v]))) res) :
    ofR (tensorGatherStep pointerBits k node ty data coords) = res := by
  unfold tensorGatherStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok d r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok cs r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok v r3 hx h3 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h3

theorem tensorScatter_sound (pointerBits : Nat) (k : Core) (node : Node) (ty : Ty)
    (init src : Nat) (coords : List Nat) (res : StepR)
    (hs : Seq (getV k init) (fun a =>
        Seq (getV k src) (fun s =>
        Seq (getVs k coords) (fun cs =>
        Seq (evalScatter pointerBits ty a s cs) (fun v =>
        Binds (next k) node.results [v])))) res) :
    ofR (tensorScatterStep pointerBits k node ty init src coords) = res := by
  unfold tensorScatterStep
  cases hs with
  | stop o hx => rw [hx]; rfl
  | ok a r1 hx h1 =>
    rw [hx, ok_bind]
    cases h1 with
    | stop o hx => rw [hx]; rfl
    | ok s r2 hx h2 =>
      rw [hx, ok_bind]
      cases h2 with
      | stop o hx => rw [hx]; rfl
      | ok cs r3 hx h3 =>
        rw [hx, ok_bind]
        cases h3 with
        | stop o hx => rw [hx]; rfl
        | ok v r4 hx h4 => rw [hx, ok_bind]; exact binds_sound _ _ _ _ h4

/-- The executable's step is a step of the relation. -/
theorem step_complete (m : Module) (k : Core) : Step m k (stepCore m k) := by
  unfold stepCore
  cases hn : nth? k.block.body k.pc with
  | none => exact Step.noTerminator hn
  | some node =>
    cases node with
    | mk inst results =>
      cases inst with
      | binop op ty l r =>
        exact Step.binop results op ty l r _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun b => seq_of_bind _ _ _ (fun v =>
            binds_complete _ ⟨.binop op ty l r, results⟩ _))))
      | unop op ty x =>
        exact Step.unop results op ty x _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun v => binds_complete _ ⟨.unop op ty x, results⟩ _)))
      | overflow op ty l r =>
        exact Step.overflow results op ty l r _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun b => seq_of_bind _ _ _ (fun vs =>
            binds_complete _ ⟨.overflow op ty l r, results⟩ _))))
      | icmp op ty l r =>
        exact Step.icmp results op ty l r _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun b => seq_of_bind _ _ _ (fun v =>
            binds_complete _ ⟨.icmp op ty l r, results⟩ _))))
      | const ty c =>
        exact Step.const results ty c _ hn (seq_of_bind _ _ _ (fun v =>
          binds_complete _ ⟨.const ty c, results⟩ _))
      | copy ty x =>
        exact Step.copy results ty x _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun u => binds_complete _ ⟨.copy ty x, results⟩ _)))
      | select ty c t e =>
        exact Step.select results ty c t e _ hn (seq_of_bind _ _ _ (fun cv =>
          seq_of_bind _ _ _ (fun tv => seq_of_bind _ _ _ (fun ev => seq_of_bind _ _ _ (fun u1 =>
            seq_of_bind _ _ _ (fun u2 => seq_of_bind _ _ _ (fun u3 =>
              selects_complete _ ⟨.select ty c t e, results⟩ _ _ _)))))))
      | extractField ty agg field =>
        exact Step.extractField results ty agg field _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun v => binds_complete _ ⟨.extractField ty agg field, results⟩ _)))
      | insertField ty agg field x =>
        exact Step.insertField results ty agg field x _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun v => seq_of_bind _ _ _ (fun w =>
            binds_complete _ ⟨.insertField ty agg field x, results⟩ _))))
      | undef ty =>
        exact Step.undef results ty _ hn (seq_of_bind _ _ _ (fun v =>
          binds_complete _ ⟨.undef ty, results⟩ _))
      | assume c =>
        exact Step.assume results c _ hn (seq_of_bind _ _ _ (fun cv =>
          seq_of_bind _ _ _ (fun b => assumes_complete _ ⟨.assume c, results⟩ b)))
      | allocaCell ty =>
        exact Step.allocaCell results ty _ hn (cellAlloc_complete _ ⟨.allocaCell ty, results⟩ ty)
      | loadCell ty x =>
        exact Step.loadCell results ty x _ hn (seq_of_bind _ _ _ (fun ptr =>
          cellAccess_complete _ ptr ty _ _ (fun c => seq_of_bind _ _ _ (fun _ =>
            binds_complete _ ⟨.loadCell ty x, results⟩ [c.value]))))
      | storeCell ty x value =>
        exact Step.storeCell results ty x value _ hn (seq_of_bind _ _ _ (fun ptr =>
          cellAccess_complete _ ptr ty _ _ (fun c => seq_of_bind _ _ _ (fun v =>
            seq_of_bind _ _ _ (fun _ => binds_complete _ ⟨.storeCell ty x value, results⟩ [])))))
      | openFrame slots =>
        exact Step.openFrame results slots _ hn (binds_complete _ ⟨.openFrame slots, results⟩ _)
      | bindSlot f slot x =>
        exact Step.bindSlot results f slot x _ hn (seq_of_bind _ _ _ (fun h =>
          seq_of_bind _ _ _ (fun ls => opened_complete _ _ _ _ _ (seq_of_bind _ _ _ (fun v =>
            slotWrite_complete _ ⟨.bindSlot f slot x, results⟩ _ _ _ _)))))
      | loadSlot f slot ty =>
        exact Step.loadSlot results f slot ty _ hn (seq_of_bind _ _ _ (fun h =>
          seq_of_bind _ _ _ (fun ls => opened_complete _ _ _ _ _
            (slotRead_complete m.pointerBits _ ⟨.loadSlot f slot ty, results⟩ _ _ _))))
      | closeFrame f =>
        exact Step.closeFrame results f _ hn (seq_of_bind _ _ _ (fun v =>
          seq_of_bind _ _ _ (fun ls => closes_complete _ ⟨.closeFrame f, results⟩ _)))
      | nullPtr => exact Step.nullPtr results _ hn (binds_complete _ ⟨.nullPtr, results⟩ _)
      | unreachable => exact Step.unreachable results hn
      | assert c kind =>
        exact Step.assert results c kind _ hn (seq_of_bind _ _ _ (fun cv =>
          seq_of_bind _ _ _ (fun u => asserts_complete _ _ _)))
      | makeClosure cid target captures =>
        exact Step.makeClosure results cid target captures _ hn (seq_of_bind _ _ _ (fun vs =>
          makesClosure_complete m k ⟨.makeClosure cid target captures, results⟩ cid target vs))
      | call callee args =>
        exact Step.call results callee args _ hn (seq_of_bind _ _ _ (fun vs =>
          calls_complete _ _ _ _ _))
      | br target args =>
        exact Step.br results target args _ hn (seq_of_bind _ _ _ (fun vs =>
          jumps_complete m.pointerBits _ _ _))
      | condBr c tT tA eT eA =>
        exact Step.condBr results c tT tA eT eA _ hn (seq_of_bind _ _ _ (fun cv =>
          seq_of_bind _ _ _ (fun u => branches_complete m.pointerBits _ _ _ _ _ _)))
      | cast op src dst x =>
        exact Step.cast results op src dst x _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun v => binds_complete _ ⟨.cast op src dst x, results⟩ _)))
      | switch x dflt dArgs cases =>
        exact Step.switch results x dflt dArgs cases _ hn (seq_of_bind _ _ _ (fun v =>
          seq_of_bind _ _ _ (fun u => switches_complete _ _ _ _ _ _)))
      | ret xs =>
        exact Step.ret results xs _ hn (seq_of_bind _ _ _ (fun vs =>
          sigChecks_complete m.pointerBits _ _ _ _ (fun _ => returns_complete _ _)))
      | alloca ty count al =>
        exact Step.alloca results ty count al _ hn (seq_of_bind _ _ _ (fun cv =>
          seq_of_bind _ _ _ (fun l => seq_of_bind _ _ _ (fun size => seq_of_bind _ _ _ (fun align =>
            allocates_complete m.pointerBits _ ⟨.alloca ty count al, results⟩ _ _)))))
      | load ty p vol al =>
        exact Step.load results ty p vol al _ hn (seq_of_bind _ _ _ (fun pv =>
          seq_of_bind _ _ _ (fun size => seq_of_bind _ _ _ (fun align => seq_of_bind _ _ _ (fun ao =>
            accesses_complete _ _ _ _ _ _ _ _
              (fun a => reads_complete _ ⟨.load ty p vol al, results⟩ _ _ _ _))))))
      | store ty p x vol al =>
        exact Step.store results ty p x vol al _ hn (seq_of_bind _ _ _ (fun pv =>
          seq_of_bind _ _ _ (fun v => seq_of_bind _ _ _ (fun size => seq_of_bind _ _ _ (fun bs =>
            seq_of_bind _ _ _ (fun align => seq_of_bind _ _ _ (fun ao =>
              accesses_complete _ _ _ _ _ _ _ _
                (fun a => binds_complete _ ⟨.store ty p x vol al, results⟩ _))))))))
      | gep ty b idx =>
        exact Step.gep results ty b idx _ hn (seq_of_bind _ _ _ (fun bv =>
          seq_of_bind _ _ _ (fun ivs => seq_of_bind _ _ _ (fun l => seq_of_bind _ _ _ (fun d =>
            seq_of_bind _ _ _ (fun ao => offsets_complete m.pointerBits _ ⟨.gep ty b idx, results⟩ _ _ _))))))
      | dealloc p =>
        exact Step.dealloc results p _ hn (seq_of_bind _ _ _ (fun pv =>
          seq_of_bind _ _ _ (fun ao => frees_complete _ ⟨.dealloc p, results⟩ _ _)))
      | tensorContract ty l r batch contract =>
        exact Step.tensorContract results ty l r batch contract _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun b => seq_of_bind _ _ _ (fun v =>
            binds_complete _ ⟨.tensorContract ty l r batch contract, results⟩ _))))
      | tensorMap ty args body =>
        exact Step.tensorMap results ty args body _ hn (seq_of_bind _ _ _ (fun vs =>
          seq_of_bind _ _ _ (fun v => binds_complete _ ⟨.tensorMap ty args body, results⟩ _)))
      | tensorReduce ty src op axes =>
        exact Step.tensorReduce results ty src op axes _ hn (seq_of_bind _ _ _ (fun a =>
          seq_of_bind _ _ _ (fun v => binds_complete _ ⟨.tensorReduce ty src op axes, results⟩ _)))
      | tensorView ty src params exprs shape index fill =>
        exact Step.tensorView results ty src params exprs shape index fill _ hn
          (seq_of_bind _ _ _ (fun a => seq_of_bind _ _ _ (fun ps => seq_of_bind _ _ _ (fun f =>
            seq_of_bind _ _ _ (fun v =>
              binds_complete _ ⟨.tensorView ty src params exprs shape index fill, results⟩ _)))))
      | tensorGather ty data coords =>
        exact Step.tensorGather results ty data coords _ hn
          (seq_of_bind _ _ _ (fun d => seq_of_bind _ _ _ (fun cs => seq_of_bind _ _ _ (fun v =>
            binds_complete _ ⟨.tensorGather ty data coords, results⟩ _))))
      | tensorScatter ty init src coords =>
        exact Step.tensorScatter results ty init src coords _ hn
          (seq_of_bind _ _ _ (fun a => seq_of_bind _ _ _ (fun s => seq_of_bind _ _ _ (fun cs =>
            seq_of_bind _ _ _ (fun v =>
              binds_complete _ ⟨.tensorScatter ty init src coords, results⟩ _)))))

/-- Every step of the relation is the executable's step. -/
theorem step_sound (m : Module) (k : Core) (r : StepR) (h : Step m k r) : stepCore m k = r := by
  unfold stepCore
  cases h with
  | noTerminator hn => rw [hn]
  | binop results op ty l rr res hn hs =>
    rw [hn]
    exact binop_sound m.pointerBits k _ op ty l rr _ hs
  | unop results op ty x res hn hs =>
    rw [hn]
    exact unop_sound m.pointerBits k _ op ty x _ hs
  | overflow results op ty l rr res hn hs =>
    rw [hn]
    exact overflow_sound m.pointerBits k _ op ty l rr _ hs
  | icmp results op ty l rr res hn hs =>
    rw [hn]
    exact icmp_sound m.pointerBits k _ op ty l rr _ hs
  | const results ty c res hn hs =>
    rw [hn]
    exact const_sound m k _ ty c _ hs
  | copy results ty x res hn hs =>
    rw [hn]
    exact copy_sound m.pointerBits k _ ty x _ hs
  | select results ty c t e res hn hs =>
    rw [hn]
    exact select_sound m.pointerBits k _ ty c t e _ hs
  | extractField results ty agg field res hn hs =>
    rw [hn]
    exact extractField_sound m k _ ty agg field _ hs
  | insertField results ty agg field x res hn hs =>
    rw [hn]
    exact insertField_sound m k _ ty agg field x _ hs
  | undef results ty res hn hs =>
    rw [hn]
    exact bind_of_seq _ _ _ _ (fun v r hb => binds_sound _ _ _ _ hb) hs
  | assume results c res hn hs =>
    rw [hn]
    exact bind_of_seq _ _ _ _ (fun cv r hc => bind_of_seq _ _ _ _
      (fun b r hb => assumes_sound _ _ b _ hb) hc) hs
  | allocaCell results ty res hn hs =>
    rw [hn]
    exact cellAlloc_sound _ _ _ _ hs
  | loadCell results ty x res hn hs =>
    rw [hn]
    exact bind_of_seq _ _ _ _ (fun ptr r hp => cellAccess_sound _ ptr ty _ _
      (fun c r hc => bind_of_seq _ _ _ _ (fun _ r hb => binds_sound _ _ _ _ hb) hc) _ hp) hs
  | storeCell results ty x value res hn hs =>
    rw [hn]
    exact bind_of_seq _ _ _ _ (fun ptr r hp => cellAccess_sound _ ptr ty _ _
      (fun c r hc => bind_of_seq _ _ _ _ (fun v r hv => bind_of_seq _ _ _ _
        (fun _ r hb => binds_sound _ _ _ _ hb) hv) hc) _ hp) hs
  | openFrame results slots res hn hb =>
    rw [hn]
    exact binds_sound _ _ _ _ hb
  | bindSlot results f slot x res hn hs =>
    rw [hn]
    exact bindSlot_sound k _ f slot x _ hs
  | loadSlot results f slot ty res hn hs =>
    rw [hn]
    exact loadSlot_sound m.pointerBits k _ f slot ty _ hs
  | closeFrame results f res hn hs =>
    rw [hn]
    exact closeFrame_sound k _ f _ hs
  | nullPtr results res hn hb =>
    rw [hn]
    exact binds_sound _ _ _ _ hb
  | unreachable results hn => rw [hn]; rfl
  | assert results c kind res hn hs =>
    rw [hn]
    exact assert_sound k _ c kind _ hs
  | makeClosure results cid target captures res hn hs =>
    rw [hn]
    exact makeClosure_sound m k _ cid target captures _ hs
  | call results callee args res hn hs =>
    rw [hn]
    exact call_sound m k _ callee args _ hs
  | br results target args res hn hs =>
    rw [hn]
    exact br_sound m.pointerBits k _ target args _ hs
  | condBr results c tT tA eT eA res hn hs =>
    rw [hn]
    exact condBr_sound m.pointerBits k _ c tT tA eT eA _ hs
  | cast results op src dst x res hn hs =>
    rw [hn]
    exact cast_sound m.pointerBits k _ op src dst x _ hs
  | switch results x dflt dArgs cases res hn hs =>
    rw [hn]
    exact switch_sound m k _ x dflt dArgs cases _ hs
  | ret results xs res hn hs =>
    rw [hn]
    exact ret_sound m.pointerBits k _ xs _ hs
  | alloca results ty count al res hn hs =>
    rw [hn]
    exact alloca_sound m.pointerBits k _ ty count al _ hs
  | load results ty p vol al res hn hs =>
    rw [hn]
    exact load_sound m.pointerBits k _ ty p vol al _ hs
  | store results ty p x vol al res hn hs =>
    rw [hn]
    exact store_sound m.pointerBits k _ ty p x vol al _ hs
  | gep results ty b idx res hn hs =>
    rw [hn]
    exact gep_sound m.pointerBits k _ ty b idx _ hs
  | dealloc results p res hn hs =>
    rw [hn]
    exact dealloc_sound k _ p _ hs
  | tensorContract results ty l rr batch contract res hn hs =>
    rw [hn]
    exact tensorContract_sound m.pointerBits k _ ty l rr batch contract _ hs
  | tensorMap results ty args body res hn hs =>
    rw [hn]
    exact tensorMap_sound m.pointerBits k _ ty args body _ hs
  | tensorReduce results ty src op axes res hn hs =>
    rw [hn]
    exact tensorReduce_sound m.pointerBits k _ ty src op axes _ hs
  | tensorView results ty src params exprs shape index fill res hn hs =>
    rw [hn]
    exact tensorView_sound m.pointerBits k _ ty src params exprs shape index fill _ hs
  | tensorGather results ty data coords res hn hs =>
    rw [hn]
    exact tensorGather_sound m.pointerBits k _ ty data coords _ hs
  | tensorScatter results ty init src coords res hn hs =>
    rw [hn]
    exact tensorScatter_sound m.pointerBits k _ ty init src coords _ hs

/-- The relation is deterministic: it has one step from each state. -/
theorem step_det (m : Module) (k : Core) (r₁ r₂ : StepR)
    (h₁ : Step m k r₁) (h₂ : Step m k r₂) : r₁ = r₂ := by
  rw [← step_sound m k r₁ h₁, ← step_sound m k r₂ h₂]

/-! ### Runs -/

/-- The executable semantics: `fuel` is the reference interpreter's
    instruction budget (`InterpretOptions::fuel`), one unit per node, checked
    before the node runs. -/
def run (m : Module) : Nat → Core → Out
  | 0, _ => .outOfFuel
  | b + 1, k =>
    match stepCore m k with
    | .done o => o
    | .cont k' => run m b k'

/-- The relational semantics: `Exec m b k o`, the run from `k` with budget
    `b` ends in verdict `o`, each step a `Step` of the relation. -/
inductive Exec (m : Module) : Nat → Core → Out → Prop where
  | outOfFuel (k : Core) : Exec m 0 k .outOfFuel
  | done (b : Nat) (k : Core) (o : Out) : Step m k (.done o) → Exec m (b + 1) k o
  | step (b : Nat) (k k' : Core) (o : Out) :
      Step m k (.cont k') → Exec m b k' o → Exec m (b + 1) k o

theorem run_sound (m : Module) : ∀ (b : Nat) (k : Core), Exec m b k (run m b k) := by
  intro b
  induction b with
  | zero => intro k; exact Exec.outOfFuel k
  | succ b ih =>
    intro k
    have hs := step_complete m k
    simp only [run]
    cases h : stepCore m k with
    | done o => rw [h] at hs; exact Exec.done b k o hs
    | cont k' => rw [h] at hs; exact Exec.step b k k' (run m b k') hs (ih k')

theorem run_complete (m : Module) (b : Nat) (k : Core) (o : Out) (h : Exec m b k o) :
    run m b k = o := by
  induction h with
  | outOfFuel k => rfl
  | done b k o hs => simp only [run, step_sound m k _ hs]
  | step b k k' o hs _ ih => simp only [run, step_sound m k _ hs]; exact ih

theorem exec_det (m : Module) (b : Nat) (k : Core) (o₁ o₂ : Out)
    (h₁ : Exec m b k o₁) (h₂ : Exec m b k o₂) : o₁ = o₂ := by
  rw [← run_complete m b k o₁ h₁, ← run_complete m b k o₂ h₂]

/-! ## Body/violation relation

These relations read the actual module and machine transitions, including the
callee body and shared cells. No CHC verdict, obligation name, hash or premise
about a producer's summary enters them. A source panic claim additionally needs
the source-to-SemR refinement at the same instance and semantic configuration.
Neither that refinement nor byte-memory refinement is supplied here. -/

inductive Reaches (m : Module) : Core → Core → Prop where
  | refl (k : Core) : Reaches m k k
  | step (a b c : Core) :
      Step m a (.cont b) → Reaches m b c → Reaches m a c

def Bad : Out → Prop
  | .ub _ | .panic _ => True
  | _ => False

/-- A bad halt after any finite number of actual body transitions. A budget
    exhaustion, unsupported construct or type error is never a safety proof. -/
def BodyViolation (m : Module) (initial : Core) : Prop :=
  ∃ current output, Reaches m initial current ∧
    Step m current (.done output) ∧ Bad output

theorem reaches_exec (m : Module) (a b : Core) (h : Reaches m a b)
    (fuel : Nat) (out : Out) (execution : Exec m fuel b out) :
    ∃ budget, Exec m budget a out := by
  induction h with
  | refl k => exact ⟨fuel, execution⟩
  | step a b c hs _ ih =>
    obtain ⟨budget, proof⟩ := ih execution
    exact ⟨budget + 1, Exec.step budget a b out hs proof⟩

/-- A terminal computation remains the same when more instruction budget is
    supplied. This does not change call-depth limits or ignore exhausted runs. -/
theorem run_terminal_extension (m : Module) (budget extra : Nat) (k : Core) (out : Out)
    (h : run m budget k = out) (terminal : out ≠ .outOfFuel) :
    run m (budget + extra) k = out := by
  induction budget generalizing k with
  | zero => simp only [run] at h; exact False.elim (terminal h.symm)
  | succ budget ih =>
    cases hs : stepCore m k with
    | done result =>
      simp only [run, hs] at h
      simp only [Nat.succ_add, run, hs]
      exact h
    | cont nextState =>
      simp only [run, hs] at h
      simp only [Nat.succ_add, run, hs]
      exact ih nextState h

/-- One checked returned execution excludes bad reachability at EVERY finite
    prefix, not just at its chosen budget. The result is about this exact SemR
    body, not about a source program or a Boolean panic placeholder. -/
theorem returned_excludes_body_violation (m : Module) (initial : Core)
    (budget : Nat) (values : List Val) (returned : run m budget initial = .ret values) :
    ¬ BodyViolation m initial := by
  intro violation
  obtain ⟨current, output, reachable, halted, bad⟩ := violation
  obtain ⟨other, execution⟩ := reaches_exec m initial current reachable 1 output
    (Exec.done 0 current output halted)
  have actual := run_complete m other initial output execution
  have notFuel : output ≠ .outOfFuel := by
    intro equality
    cases equality
    exact bad
  have left := run_terminal_extension m budget other initial (.ret values) returned (by
    intro equality
    cases equality)
  have right := run_terminal_extension m other budget initial output actual notFuel
  rw [Nat.add_comm other budget] at right
  have same : output = .ret values := right.symm.trans left
  cases same
  exact bad

/-- Start a run of function `fid` on `args` (`execute_func`). -/
def start (m : Module) (fid : Nat) (args : List Val) (depth : Nat) : R Core :=
  match m.functions.find? (fun f => f.id == fid) with
  | none => tyR "MissingFunction: function not found"
  | some f =>
    match nth? m.funcTys f.ty with
    | none => tyR "SignatureMismatch: undefined signature"
    | some sig =>
      if f.blocks.isEmpty then unsupR "interprocedural_call"
      else if sig.vararg then tyR "SignatureMismatch: variadic definition"
      else if !m.executableTarget then unsupR "target.byte_model"
      else do
        checkSig m.pointerBits args sig.params
        match findBlock f.blocks f.entry with
        | none => tyR "MissingBlock: entry block not found"
        | some b => do
          let env ← bindParams m.pointerBits [] b.params args
          pure { fn := f, sig := sig, block := b, pc := 0, env := env, depth := depth,
                 stack := [], openFrames := [], nextFrame := 0, mem := Mem.empty }

/-- A whole run of function `fid` on `args` with instruction budget `fuel`
    and call depth `depth` (`InterpretOptions::{fuel, max_call_depth}`). -/
def runFunction (m : Module) (fid : Nat) (args : List Val) (fuel depth : Nat) : Out :=
  match start m fid args depth with
  | .stop o => o
  | .ok k => run m fuel k

/-! ## The binary decoder (`trust_ir::binary`, header `TRUST_IR`, v38–v70)

The input is the blob's bytes as `Nat`s (each `< 256`). The decoder reads
exactly what `deserialize_module` reads, with every version gate of the path
it follows, and is total: each repetition is bounded by a count that is
itself bounded by the bytes remaining (`reserve_checked`), and nested
constants by the input length. A construct outside the fragment is
`unsupported`; bytes the Rust reader refuses are `malformed`. -/

inductive DErr where
  | unsupported (feature : String)
  | malformed (msg : String)

inductive DRes (α : Type) where
  | ok (a : α) (rest : List Nat)
  | err (e : DErr)

/-- The decoder monad: the wire version, the validated UTF-8 string pool, and the
    remaining bytes. -/
def P (α : Type) : Type := Nat → Array (List Nat) → List Nat → DRes α

def P.pure {α : Type} (a : α) : P α := fun _ _ bs => .ok a bs

def P.bind {α β : Type} (x : P α) (f : α → P β) : P β := fun v n bs =>
  match x v n bs with
  | .ok a rest => f a v n rest
  | .err e => .err e

def P.map {α β : Type} (f : α → β) (x : P α) : P β := fun v n bs =>
  match x v n bs with
  | .ok a rest => .ok (f a) rest
  | .err e => .err e

instance : Monad P where
  pure := P.pure
  bind := P.bind
  map := P.map
  mapConst := fun a x => P.map (fun _ => a) x
  seq := fun f x => P.bind f (fun g => P.map g (x ()))
  seqLeft := fun x y => P.bind x (fun a => P.map (fun _ => a) (y ()))
  seqRight := fun x y => P.bind x (fun _ => y ())

def bad {α : Type} (msg : String) : P α := fun _ _ _ => .err (.malformed msg)
def unsup {α : Type} (f : String) : P α := fun _ _ _ => .err (.unsupported f)
def version : P Nat := fun v _ bs => .ok v bs
def stringPool : P (Array (List Nat)) := fun _ pool bs => .ok pool bs
def remaining : P Nat := fun _ _ bs => .ok bs.length bs

def u8 : P Nat := fun _ _ bs =>
  match bs with
  | b :: rest => .ok b rest
  | [] => .err (.malformed "unexpected end of input")

/-- `n` bytes, little-endian, as a number. -/
def leN : Nat → P Nat
  | 0 => pure 0
  | n + 1 => do let b ← u8; let r ← leN n; pure (b + 256 * r)

def u32 : P Nat := leN 4
def u64 : P Nat := leN 8

/-- `read_v64`: shortest LEB128, at most ten bytes, one payload bit in the
    tenth. -/
def v64Loop : Nat → Nat → Nat → P Nat
  | 0, _, _ => bad "varint overflow"
  | fuel + 1, shift, acc => do
    let b ← u8
    let payload := b % 128
    if shift == 63 && 1 < payload then bad "varint overflow"
    else
      let acc' := acc + payload * 2 ^ shift
      if b < 128 then
        if shift != 0 && payload == 0 then bad "non-canonical varint encoding"
        else pure acc'
      else v64Loop fuel (shift + 7) acc'

def v64 : P Nat := v64Loop 10 0 0

def v32 : P Nat := do
  let x ← v64
  if x < 2 ^ 32 then pure x else bad "varint overflow"

/-- `read_checked_len`: a count no larger than the bytes left. -/
def checkedLen : P Nat := do
  let n ← v32
  let r ← remaining
  if n ≤ r then pure n else bad "declared count exceeds the input"

def boolB : P Bool := do
  let b ← u8
  if b == 0 then pure false else if b == 1 then pure true else bad "invalid bool tag"

def rep {α : Type} : Nat → P α → P (List α)
  | 0, _ => pure []
  | n + 1, p => do let a ← p; let as ← rep n p; pure (a :: as)

def counted {α : Type} (p : P α) : P (List α) := do
  let n ← checkedLen
  rep n p

/-- One UTF-8 scalar's continuation bytes. -/
def contBytes : Nat → List Nat → Option (List Nat)
  | 0, bs => some bs
  | n + 1, b :: bs => if 128 ≤ b && b < 192 then contBytes n bs else none
  | _ + 1, [] => none

/-- UTF-8 validity (Rust's `String::from_utf8`): shortest forms, no
    surrogates, nothing past U+10FFFF. -/
def utf8Ok : Nat → List Nat → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | fuel + 1, b :: bs =>
    if b < 128 then utf8Ok fuel bs
    else if 194 ≤ b && b < 224 then
      match contBytes 1 bs with | some r => utf8Ok fuel r | none => false
    else if 224 ≤ b && b < 240 then
      match bs with
      | c :: _ =>
        if (b == 224 && c < 160) || (b == 237 && 160 ≤ c) then false
        else match contBytes 2 bs with | some r => utf8Ok fuel r | none => false
      | [] => false
    else if 240 ≤ b && b < 245 then
      match bs with
      | c :: _ =>
        if (b == 240 && c < 144) || (b == 244 && 144 ≤ c) then false
        else match contBytes 3 bs with | some r => utf8Ok fuel r | none => false
      | [] => false
    else false

def rawStr : P (List Nat) := do
  let n ← checkedLen
  let bytes ← rep n u8
  if utf8Ok bytes.length bytes then pure bytes else bad "invalid UTF-8"

def strBytes : P (List Nat) := do
  let id ← v32
  let pool ← stringPool
  match pool[id]? with
  | some bytes => pure bytes
  | none => bad "bad string id"

/-- `read_str` once the pool exists: an id into it. -/
def strIdV : P Nat := do
  let id ← v32
  let pool ← stringPool
  if id < pool.size then pure id else bad "bad string id"

def strId : P Unit := do let _ ← strIdV; pure ()

def optStr : P Unit := do
  let t ← u8
  if t == 0 then pure () else if t == 1 then strId else bad "invalid tag"

def optBytes : P (Option (List Nat)) := do
  let t ← u8
  if t == 0 then pure none
  else if t == 1 then do let s ← strBytes; pure (some s)
  else bad "invalid tag"

/-- `read_target_info`, including all ABI fields of the supported wire
    versions (v38+). Transport never claims the layout is executable. -/
def targetInfo : P (Option TargetInfo) := do
  let tag ← u8
  if tag == 0 then pure none
  else if tag == 1 then do
    let triple ← strBytes
    let pointerSize ← v32
    let endian ← u8
    if 1 < endian then bad "invalid endianness tag" else do
      let abi ← optBytes
      let structPassing ← u8
      if 2 < structPassing then bad "invalid struct passing tag" else
        pure (some { triple := triple, pointerSize := pointerSize,
                     bigEndian := endian == 1, abi := abi, structPassing := structPassing })
  else bad "invalid tag"

def optV64 : P Unit := do
  let t ← u8
  if t == 0 then pure () else if t == 1 then do let _ ← v64; pure () else bad "invalid tag"

/-- `read_opt_u64`. -/
def optU64 : P (Option Nat) := do
  let t ← u8
  if t == 0 then pure none
  else if t == 1 then do let x ← v64; pure (some x)
  else bad "invalid tag"

/-- A tensor's element type (`Ty::Tensor`, v67): one `read_ty` tag. Only an
    integer element is in the fragment. A float element is refused by name
    (SemR has no float model), every other type the format has as
    `tensor.element`, and a tag it has not is `malformed`. -/
def tensorElem : P IntTy := do
  let t ← u8
  match t with
  | 0 => pure .i8 | 1 => pure .i16 | 2 => pure .i32 | 3 => pure .i64 | 4 => pure .i128
  | 5 => pure .u8 | 6 => pure .u16 | 7 => pure .u32 | 8 => pure .u64 | 9 => pure .u128
  | 33 => pure .isize | 34 => pure .usize
  | 10 | 11 | 31 => unsup "tensor.float_element"
  | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28
  | 29 | 30 | 32 | 35 | 36 | 37 | 38 | 40 | 41 | 255 => unsup "tensor.element"
  | _ => bad "invalid Ty tag"

/-- `read_ty`, the fragment's tags; every other tag the format has is
    `unsupported`, every byte it has not is `malformed`. -/
def ty : P Ty := do
  let wireVersion ← version
  let t ← u8
  match t with
  | 0 => pure (.int .i8) | 1 => pure (.int .i16) | 2 => pure (.int .i32)
  | 3 => pure (.int .i64) | 4 => pure (.int .i128) | 5 => pure (.int .u8)
  | 6 => pure (.int .u16) | 7 => pure (.int .u32) | 8 => pure (.int .u64)
  | 9 => pure (.int .u128) | 12 => pure .bool | 13 => pure .ptr
  | 14 => pure .unit | 15 => pure .never
  | 16 => do let id ← v32; pure (.struct id)
  | 19 => do let id ← v32; pure (.enum id)
  | 33 => pure (.int .isize) | 34 => pure (.int .usize)
  | 10 | 11 | 31 => unsup "ty.float"
  | 40 => do
    if wireVersion < 64 then bad "invalid Ty tag"
    else
      let size ← v64
      let align ← v64
      if storageGeometry 64 size align then unsup "ty.storage"
      else bad "invalid storage geometry"
  | 41 => do
    if wireVersion < 67 then bad "invalid Ty tag"
    else
      let rank ← v32
      let e ← tensorElem
      pure (.tensor e rank)
  | 35 => unsup "ty.char"
  | 17 | 18 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 32 | 36
  | 37 | 38 | 255 => unsup "ty.compound"
  | _ => bad "invalid Ty tag"

/-- Scalar entries in the producer's interned type catalog carry no lookup
    semantics: instruction types are encoded inline. Refuse every non-scalar
    entry rather than guessing the meaning of a referenced/compound type. -/
def scalarMetadataType : P Unit := do
  match ← ty with
  | .int _ | .bool => pure ()
  | _ => unsup "types.non_scalar"

/-- `read_constant`, the fragment's tags. -/
def constant : Nat → P Const
  | 0 => bad "constant nesting exceeds the input"
  | fuel + 1 => do
    let t ← u8
    match t with
    | 0 => do let p ← leN 16; pure (.int p)
    | 2 => do let b ← boolB; pure (.bool b)
    | 3 => do
      let n ← checkedLen
      let es ← rep n (constant fuel)
      pure (.aggregate es)
    | 1 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 255 =>
      unsup "constant.compound"
    | 18 => do
      let v ← version
      if v < 70 then bad "invalid Constant tag" else do
        let d ← rep 32 u8
        let n ← checkedLen
        let dims ← rep n u64
        pure (.tensorBlob d dims)
    | _ => bad "invalid Constant tag"

/-- The v70 tag reads the 32 digest bytes and the counted `u64` extents (a
    `[2, 3]` tensor of an all-`7` digest), and below v70 it is the reader's
    unknown tag. -/
theorem tensor_blob_tag_decodes :
    constant 1 70 #[] ([18] ++ List.replicate 32 7 ++ [2, 2, 0, 0, 0, 0, 0, 0, 0,
        3, 0, 0, 0, 0, 0, 0, 0]) = .ok (.tensorBlob (List.replicate 32 7) [2, 3]) [] ∧
      constant 1 69 #[] [18] = .err (.malformed "invalid Constant tag") := ⟨rfl, rfl⟩

def binop : P BinOp := do
  let t ← u8
  match t with
  | 0 => pure .add | 1 => pure .sub | 2 => pure .mul | 3 => pure .udiv | 4 => pure .sdiv
  | 5 => pure .urem | 6 => pure .srem | 12 => pure .and | 13 => pure .or | 14 => pure .xor
  | 15 => pure .shl | 16 => pure .lshr | 17 => pure .ashr
  | 20 => pure .bAnd | 21 => pure .bOr | 22 => pure .bXor
  | 7 | 8 | 9 | 10 | 11 | 18 | 19 => unsup "binop.float"
  | 23 => do let v ← version; if 51 ≤ v then pure .rotl else bad "invalid BinOp tag"
  | 24 => do let v ← version; if 51 ≤ v then pure .rotr else bad "invalid BinOp tag"
  | 25 => do let v ← version; if 51 ≤ v then unsup "binop.float" else bad "invalid BinOp tag"
  | _ => bad "invalid BinOp tag"

def unop : P UnOp := do
  let t ← u8
  match t with
  | 0 => pure .neg | 2 => pure .not | 3 => pure .ctpop
  | 1 | 4 | 5 | 6 | 7 | 8 => unsup "unop.float"
  | 9 => do let v ← version; if 51 ≤ v then pure .ctlz else bad "invalid UnOp tag"
  | 10 => do let v ← version; if 51 ≤ v then pure .cttz else bad "invalid UnOp tag"
  | 11 => do let v ← version; if 51 ≤ v then pure .bswap else bad "invalid UnOp tag"
  | 12 => do let v ← version; if 51 ≤ v then pure .bitreverse else bad "invalid UnOp tag"
  | _ => bad "invalid UnOp tag"

def icmpop : P ICmpOp := do
  let t ← u8
  match t with
  | 0 => pure .eq | 1 => pure .ne | 2 => pure .ult | 3 => pure .ule | 4 => pure .ugt
  | 5 => pure .uge | 6 => pure .slt | 7 => pure .sle | 8 => pure .sgt | 9 => pure .sge
  | _ => bad "invalid ICmpOp tag"

def ovfop : P OvfOp := do
  let t ← u8
  match t with
  | 0 => pure .add | 1 => pure .sub | 2 => pure .mul
  | _ => bad "invalid OverflowOp tag"

def ids : P (List Nat) := counted v32

/-- `read_tensor_map_node` (v68): the `TensorMapNode` tag, then the scalar
    instruction's fields in its order, the operator by the scalar
    instruction's own tag (so a float operator or type is `unsupported` by
    the scalar decoders' names) and each lane a `v32`. -/
def mapNode : P MapNode := do
  let t ← u8
  match t with
  | 0 => do let op ← binop; let τ ← ty; let l ← v32; let r ← v32; pure (.binop op τ l r)
  | 1 => do let op ← unop; let τ ← ty; let x ← v32; pure (.unop op τ x)
  | 2 => do let op ← icmpop; let τ ← ty; let l ← v32; let r ← v32; pure (.icmp op τ l r)
  | 3 => do let τ ← ty; let c ← v32; let tl ← v32; let el ← v32; pure (.select τ c tl el)
  | 4 => do
    let o ← u8
    if 16 < o then bad "invalid CastOp tag" else do
    let srcTy ← ty
    let dstTy ← ty
    let x ← v32
    match o with
    | 0 => pure (.cast .trunc srcTy dstTy x)
    | 1 => pure (.cast .zext srcTy dstTy x)
    | 2 => pure (.cast .sext srcTy dstTy x)
    | 11 => pure (.cast .bitcast srcTy dstTy x)
    | _ => unsup "inst.cast"
  | _ => bad "invalid TensorMapNode tag"

/-- `read_tensor_reduce_op` (v68): the `TensorReduceOp` tags `0..=8`. -/
def reduceOp : P ReduceOp := do
  let t ← u8
  match t with
  | 0 => pure .add | 1 => pure .mul | 2 => pure .and | 3 => pure .or | 4 => pure .xor
  | 5 => pure .smin | 6 => pure .smax | 7 => pure .umin | 8 => pure .umax
  | _ => bad "invalid TensorReduceOp tag"

/-- `read_tensor_index_expr` (v68): the `TensorIndexExpr` tag, then a `v64`
    literal, a `v32` index, or two `v32` node ids. -/
def ixExpr : P IxExpr := do
  let t ← u8
  match t with
  | 0 => do let n ← v64; pure (.lit n)
  | 1 => do let k ← v32; pure (.param k)
  | 2 => do let j ← v32; pure (.srcExtent j)
  | 3 => do let i ← v32; pure (.coord i)
  | 4 => do let a ← v32; let b ← v32; pure (.add a b)
  | 5 => do let a ← v32; let b ← v32; pure (.sub a b)
  | 6 => do let a ← v32; let b ← v32; pure (.mul a b)
  | 7 => do let a ← v32; let b ← v32; pure (.div a b)
  | 8 => do let a ← v32; let b ← v32; pure (.rem a b)
  | 9 => do let a ← v32; let b ← v32; pure (.min a b)
  | 10 => do let a ← v32; let b ← v32; pure (.max a b)
  | _ => bad "invalid TensorIndexExpr tag"

/-- `read_inst`, the fragment's tags; every other instruction the format has
    is `unsupported` by its family. -/
def inst : P Inst := do
  let t ← u8
  match t with
  | 0 => do let op ← binop; let τ ← ty; let a ← v32; let b ← v32; pure (.binop op τ a b)
  | 1 => do let op ← unop; let τ ← ty; let a ← v32; pure (.unop op τ a)
  | 2 => do let op ← ovfop; let τ ← ty; let a ← v32; let b ← v32; pure (.overflow op τ a b)
  | 3 => do let op ← icmpop; let τ ← ty; let a ← v32; let b ← v32; pure (.icmp op τ a b)
  | 15 => do let tg ← v32; let xs ← ids; pure (.br tg xs)
  | 16 => do
    let c ← v32; let tt ← v32; let ta ← ids; let et ← v32; let ea ← ids
    pure (.condBr c tt ta et ea)
  | 20 => do let vs ← ids; pure (.ret vs)
  | 21 => do let τ ← ty; let a ← v32; let f ← v32; pure (.extractField τ a f)
  | 22 => do let τ ← ty; let a ← v32; let f ← v32; let x ← v32; pure (.insertField τ a f x)
  | 25 => do let τ ← ty; let r ← remaining; let c ← constant (r + 1); pure (.const τ c)
  | 26 => pure .nullPtr
  | 31 => do let τ ← ty; let a ← v32; pure (.copy τ a)
  | 32 => do let τ ← ty; let c ← v32; let a ← v32; let b ← v32; pure (.select τ c a b)
  | 40 => do
    let _ ← v32
    strId
    let slots ← counted (do strId; ty)
    pure (.openFrame slots)
  | 41 => do let f ← v32; let s ← v32; let x ← v32; pure (.bindSlot f s x)
  | 42 => do let f ← v32; let s ← v32; let τ ← ty; pure (.loadSlot f s τ)
  | 43 => do let f ← v32; pure (.closeFrame f)
  | 4 => unsup "inst.fcmp"
  | 5 => do
    let o ← u8
    if 16 < o then bad "invalid CastOp tag" else do
    let src ← ty
    let dst ← ty
    let x ← v32
    match o with
    | 0 => pure (.cast .trunc src dst x)
    | 1 => pure (.cast .zext src dst x)
    | 2 => pure (.cast .sext src dst x)
    | 11 => pure (.cast .bitcast src dst x)
    | _ => unsup "inst.cast"
  | 6 => do
    let τ ← ty; let p ← v32; let vol ← boolB; let al ← optU64
    pure (.load τ p vol al)
  | 7 => do
    let τ ← ty; let p ← v32; let x ← v32; let vol ← boolB; let al ← optU64
    pure (.store τ p x vol al)
  | 8 => do
    let τ ← ty
    let hc ← u8
    let c ← (if hc == 0 then pure none else do let c ← v32; pure (some c) : P (Option Nat))
    let al ← optU64
    pure (.alloca τ c al)
  | 9 => do
    -- `inbounds` (v8+): read and ignored, as the interpreter ignores it (MiniRust's
    -- in-bounds offset is undefined behaviour out of bounds: a divergence, see the header).
    let τ ← ty; let b ← v32; let xs ← ids; let _ ← boolB
    pure (.gep τ b xs)
  | 39 => do let p ← v32; pure (.dealloc p)
  | 10 | 11 | 12 | 13 | 14 | 45 | 46 | 47 | 48 | 49 | 61 | 62 =>
    unsup "inst.memory"
  | 17 => do
    let v ← version
    let x ← v32
    let dflt ← v32
    let dArgs ← ids
    let cases ← counted (do
      let r ← remaining
      let c ← constant (r + 1)
      let t ← v32
      let as ← ids
      pure (c, t, as))
    if 15 ≤ v then do let _ ← boolB; pure () else pure ()
    pure (.switch x dflt dArgs cases)
  | 18 => do let f ← v32; let xs ← ids; pure (.call f xs)
  | 19 | 51 | 64 | 65 | 69 => unsup "inst.call"
  | 23 | 24 | 59 | 60 => unsup "inst.aggregate"
  | 27 => unsup "inst.undef"
  | 28 => do let c ← v32; pure (.assume c)
  | 29 => do let c ← v32; pure (.assert c .unspecified)
  | 63 => do
    let v ← version
    if v < 52 then bad "invalid Inst tag" else do
    let c ← v32
    let kt ← u8
    let kind ← (match kt with
      | 0 => do
        let op ← u8
        if op ≤ 7 then pure (AssertKind.overflow op) else bad "invalid assert overflow op"
      | 1 => pure .divByZero
      | 2 => pure .remByZero
      | 3 => do let i ← v32; let l ← v32; pure (.bounds i l)
      | 4 => do let r ← v32; let f ← v32; pure (.misaligned r f)
      | 5 => pure .nullPtr
      | _ => bad "invalid AssertKind tag" : P AssertKind)
    pure (.assert c kind)
  | 66 | 67 => unsup "inst.assert.sited"
  | 30 => pure .unreachable
  | 33 | 34 | 35 => unsup "inst.borrow"
  | 36 | 37 | 38 => unsup "inst.arc"
  | 44 => unsup "inst.dialect"
  | 50 => unsup "inst.coroutine"
  | 52 | 53 => unsup "inst.unwind"
  | 54 | 55 | 56 => unsup "inst.sequence"
  | 57 | 58 | 68 => unsup "inst.drop"
  -- v63 adds ONLY runtime MakeClosure (tag70, closureTyId/FuncId/captures).
  -- Its table/value execution remains outside this binary fragment. Existing
  -- scalar payloads at the current writer version have unchanged semantics.
  | 70 => do
    let v ← version
    if 63 ≤ v then unsup "inst.make_closure" else bad "invalid Inst tag"
  -- v67: `TensorContract` (result type, operands, then the batch and the
  -- contracted axis pairs, each a counted list of `(v32, v32)`).
  | 71 => do
    let v ← version
    if v < 67 then bad "invalid Inst tag" else do
    let τ ← ty
    let a ← v32
    let b ← v32
    let batch ← counted (do let x ← v32; let y ← v32; pure (x, y))
    let contract ← counted (do let x ← v32; let y ← v32; pure (x, y))
    pure (.tensorContract τ a b batch contract)
  -- v68: `TensorMap` (result type, the counted operands, the counted body),
  -- `TensorReduce` (result type, source, operator, counted axes, the order:
  -- `RowMajor`, tag 0, the only one) and `TensorView` (result type, source,
  -- counted parameters, counted nodes, counted shape and index node ids, then
  -- the fill: `0`, or `1` and its value id).
  | 72 => do
    let v ← version
    if v < 68 then bad "invalid Inst tag" else do
    let τ ← ty
    let args ← ids
    let body ← counted mapNode
    pure (.tensorMap τ args body)
  | 73 => do
    let v ← version
    if v < 68 then bad "invalid Inst tag" else do
    let τ ← ty
    let src ← v32
    let op ← reduceOp
    let axes ← counted v32
    let order ← u8
    if order != 0 then bad "invalid TensorReduceOrder tag" else do
    pure (.tensorReduce τ src op axes)
  | 74 => do
    let v ← version
    if v < 68 then bad "invalid Inst tag" else do
    let τ ← ty
    let src ← v32
    let params ← ids
    let exprs ← counted ixExpr
    let shape ← counted v32
    let index ← counted v32
    let ft ← u8
    let fill ← (if ft == 0 then pure none
      else if ft == 1 then do let f ← v32; pure (some f)
      else bad "invalid tag" : P (Option Nat))
    pure (.tensorView τ src params exprs shape index fill)
  -- v69: `TensorGather` (result type, data, the counted coordinate tensors)
  -- and `TensorScatter` (result type, init, source, the counted coordinate
  -- tensors).
  | 75 => do
    let v ← version
    if v < 69 then bad "invalid Inst tag" else do
    let τ ← ty
    let data ← v32
    let coords ← ids
    pure (.tensorGather τ data coords)
  | 76 => do
    let v ← version
    if v < 69 then bad "invalid Inst tag" else do
    let τ ← ty
    let init ← v32
    let src ← v32
    let coords ← ids
    pure (.tensorScatter τ init src coords)
  | _ => bad "invalid Inst tag"

/-- The v69 tags read their operands in field order (a `tensor<i32, 1>`
    gather of `%3` at `[%4, %5]`, a `tensor<u8, 1>` scatter of `%1` over `%0`
    at `[%2]`), and below v69 each is the reader's unknown tag. -/
theorem tensor_gather_scatter_tags_decode :
    inst 69 #[] [75, 41, 1, 2, 3, 2, 4, 5] = .ok (.tensorGather (.tensor .i32 1) 3 [4, 5]) [] ∧
      inst 69 #[] [76, 41, 1, 5, 0, 1, 1, 2] = .ok (.tensorScatter (.tensor .u8 1) 0 1 [2]) [] ∧
      inst 68 #[] [75] = .err (.malformed "invalid Inst tag") ∧
      inst 68 #[] [76] = .err (.malformed "invalid Inst tag") := ⟨rfl, rfl, rfl, rfl⟩

/-- `read_proof_annotation`: a producer's claim about a node, decoded and
    ignored (no annotation changes a run, and none is trusted). -/
def proofAnnotation : P Unit := do
  let t ← u8
  if t ≤ 15 || t == 18 || t == 19 || t == 21 || t == 22 || (24 ≤ t && t ≤ 27) || t == 33 ||
      (35 ≤ t && t ≤ 38) then pure ()
  else if t == 16 then do
    let o ← u8
    if o ≤ 4 then pure () else bad "invalid Ordering tag"
  else if t == 17 || t == 31 || t == 32 then do
    let _ ← leN (if t == 17 then 16 else 32); pure ()
  else if t == 20 || t == 28 then do let _ ← u64; pure ()
  else if t == 23 || t == 30 then do let _ ← v32; pure ()
  else if t == 29 then do
    let d ← u8
    if d ≤ 2 then pure () else bad "invalid Divergence tag"
  else if t == 34 then do let _ ← counted v32; pure ()
  else bad "invalid ProofAnnotation tag"

/-- A presence byte whose payload the fragment does not carry. -/
def absent (feature : String) : P Unit := do
  let t ← u8
  if t == 0 then pure () else if t == 1 then unsup feature else bad "invalid tag"

/-- `read_instr_node`: the instruction, its results, then the proof, span,
    proof-context (v6+) and scope (v33+) side records, which carry no
    semantics; proof annotations and proof contexts are refused. -/
def node : P Node := do
  let i ← inst
  let rs ← ids
  let np ← checkedLen
  let _ ← rep np proofAnnotation
  let sp ← u8
  if sp == 1 then do let _ ← v32; let _ ← v32; let _ ← v32; pure ()
  else if sp != 0 then bad "invalid tag" else pure ()
  absent "proof_context"
  let sc ← u8
  if sc == 1 then do let _ ← v32; pure () else if sc != 0 then bad "invalid tag" else pure ()
  pure { inst := i, results := rs }

def block : P Block := do
  let id ← v32
  let ps ← counted (do let x ← v32; let τ ← ty; pure (x, τ))
  let body ← counted node
  pure { id := id, params := ps, body := body }

/-- `read_pass_mode` (v45+). -/
def passMode : P Unit := do
  let t ← u8
  if t ≤ 3 then pure ()
  else if t == 4 then do let _ ← counted ty; pure ()
  else if t == 5 then do let _ ← boolB; pure ()
  else bad "invalid tag"

/-- `read_param_attrs`: decoded and ignored (no attribute changes a run). -/
def paramAttrs : P Unit := do
  let v ← version
  let flags ← u8
  let allocated := 7 + (if 20 ≤ v then 24 else 0) + (if 45 ≤ v then 96 else 0)
  if Nat.land flags (255 - allocated) != 0 then bad "unallocated parameter attribute bits"
  if Nat.land flags 96 == 96 then bad "both zeroext and signext"
  optV64
  optV64
  if 45 ≤ v then passMode else pure ()

def funcAttrs : P Unit := do
  let v ← version
  let flags ← u8
  if Nat.land flags 16 != 0 && v < 41 then bad "naked requires v41"
  let _ ← counted paramAttrs
  if 41 ≤ v then do let _ ← counted strId; pure () else pure ()
  if 45 ≤ v then paramAttrs else pure ()

def callingConv : P Unit := do
  let v ← version
  let t ← u8
  if t ≤ 4 || (t ≤ 11 && 45 ≤ v) then pure () else bad "invalid calling convention"

def linkage : P Unit := do
  let v ← version
  let t ← u8
  if t ≤ 4 || (t ≤ 8 && 41 ≤ v) then pure () else bad "invalid linkage"

def span : P Unit := do let _ ← v32; let _ ← v32; let _ ← v32; pure ()

def func : P Func := do
  let v ← version
  let id ← v32
  let name ← strBytes
  let fty ← v32
  let entry ← v32
  let bs ← counted block
  let np ← checkedLen
  let _ ← rep np proofAnnotation
  callingConv
  linkage
  funcAttrs
  absent "function_summary"
  -- v23 producer provenance: decoded and ignored (no producer changes a run)
  let pr ← u8
  if pr == 1 then do
    let tag ← u8
    if tag ≤ 4 then pure () else if tag == 5 then strId else bad "invalid producer tag"
  else if pr != 0 then bad "invalid tag" else pure ()
  -- v32 value names
  let vn ← u8
  if vn == 1 then do let _ ← counted (do let _ ← v32; strId); pure ()
  else if vn != 0 then bad "invalid tag" else pure ()
  -- v33 scope tree
  let st ← u8
  if st == 1 then do
    let _ ← counted (do
      let p ← u8
      if p == 1 then do let _ ← v32; pure () else if p != 0 then bad "invalid tag" else pure ()
      let s ← u8
      if s == 1 then span else if s != 0 then bad "invalid tag" else pure ())
    pure ()
  else if st != 0 then bad "invalid tag" else pure ()
  absent "source_provenance"
  if 41 ≤ v then do
    let g ← u8
    if g == 0 || g == 1 then pure ()
    else if g == 2 then strId
    else if g == 3 && 61 ≤ v then unsup "body_gate.evidence"
    else bad "invalid body gate tag"
    optStr
  else pure ()
  if 45 ≤ v then do
    optStr
    let vis ← u8
    if vis ≤ 2 then pure () else bad "invalid visibility"
    let _ ← boolB
    pure ()
  else pure ()
  pure { id := id, ty := fty, entry := entry, blocks := bs, name := name }

def funcTy : P FuncTy := do
  let v ← version
  let ps ← counted ty
  let rs ← counted ty
  let va ← boolB
  if 60 ≤ v then do
    let abi ← boolB
    if abi then unsup "signature_abi" else pure ()
  else pure ()
  pure { params := ps, returns := rs, vararg := va }

/-- `EnumTagRepr`'s wire byte: `1..=8` are `u8…u64, i8…i64`; `9`/`10`
    (`u128`/`i128`, v45+) are outside the fragment. -/
def tagRepr (b : Nat) : P (Option IntTy) := do
  let v ← version
  match b with
  | 1 => pure (some .u8) | 2 => pure (some .u16) | 3 => pure (some .u32) | 4 => pure (some .u64)
  | 5 => pure (some .i8) | 6 => pure (some .i16) | 7 => pure (some .i32) | 8 => pure (some .i64)
  | 9 | 10 => if 45 ≤ v then unsup "enum.repr128" else bad "invalid tag"
  | _ => bad "invalid tag"

/-- `EnumDef::effective_discriminants`: explicit, or one more than the
    previous (the first `0`); `none` on a duplicate. (`i128` overflow of the
    increment needs an explicit `i128::MAX`, which no tag below 128 bits
    fits, so it is refused with the tag.) -/
def effDiscs : List (Option Int) → Nat → Int → List Int → Option (List Int)
  | _, 0, _, acc => some acc.reverse
  | ds, n + 1, next, acc =>
    let v := match ds with
      | some x :: _ => x
      | _ => next
    if acc.contains v then none else effDiscs ds.tail n (v + 1) (v :: acc)

/-- `EnumTagRepr::fits`. `tagRepr` admits only fixed-width tags, so its
    width does not depend on target metadata parsed later in the module. -/
def fitsTag (t : IntTy) (d : Int) : Bool :=
  if t.signed then decide (-(half (t.bits 64) : Int) ≤ d) && decide (d < (half (t.bits 64) : Int))
  else decide (0 ≤ d) && decide (d < (modulus (t.bits 64) : Int))

def listMin : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

/-- `EnumDef::canonical_tag_repr` (`EnumTagRepr::smallest_for`). -/
def canonTag (repr : Option IntTy) (discs : List Int) : Option IntTy :=
  match repr with
  | some t => if discs.all (fitsTag t) then some t else none
  | none =>
    let lo := listMin discs
    let hi := listMax discs
    let cands : List IntTy := if 0 ≤ lo then [.u8, .u16, .u32, .u64] else [.i8, .i16, .i32, .i64]
    cands.find? (fun t => fitsTag t lo && fitsTag t hi)

/-- A tag's byte size, which on every target the interpreter executes is
    also its alignment. -/
def tagBytes (t : IntTy) : Nat := t.bits 64 / 8

/-- Flat logical scalar structs, without physical layout or nominal-origin
    claims. Nested/opaque/pointer fields and every explicit layout stay refused. -/
def flatStructDef : P StructDef := do
  let v ← version
  let id ← v32
  strId
  let n ← checkedLen
  if 128 < n then unsup "struct.field_count" else pure ()
  let fs ← rep n (do
    strId
    let t ← ty
    if !isScalarTy t || t.beq .ptr then unsup "struct.field_type" else pure ()
    absent "struct.field_offset"
    pure t)
  absent "struct.size"
  absent "struct.align"
  if 10 ≤ v then do
    let r ← u8
    if r == 0 then pure ()
    else if r ≤ 3 then unsup "struct.repr" else bad "invalid StructRepr tag"
  else pure ()
  if 58 ≤ v then absent "struct.origin" else pure ()
  pure { id := id, fields := fs }

/-- `read_enum_def`. An enum with no explicit discriminant, no `repr` and no
    layout record decodes as v0 did (implicit `0…n-1`, tag `u8`, scalar
    payloads). One with any of them is decoded only when it is FIELDLESS
    (D-2(b)), with a well-formed discriminant assignment and canonical tag, and
    with no layout record or the direct layout the reference interpreter
    accepts for it (tag at offset 0, size and alignment the tag's, no field
    offsets); anything else is `unsupported` by name. Wire65 SingleInhabited
    consumes its selector but remains an unsupported physical layout here; an
    empty nominal declaration remains unsupported without fabricating a tag. -/
def enumDef : P EnumDef := do
  let v ← version
  let id ← v32
  strId
  let vs ← counted (do
    strId
    let fs ← counted ty
    let _ ← counted strId
    pure ({ fields := fs } : Variant))
  let nd ← checkedLen
  let ds ← rep nd (do
    let t ← u8
    if t == 0 then pure (none : Option Int)
    else if t == 1 then do let p ← leN 16; pure (some (i128Of p))
    else bad "invalid tag")
  let rb ← u8
  let repr ← (if rb == 0 then pure none else tagRepr rb : P (Option IntTy))
  let lb ← u8
  -- the layout record: `none`, or `(direct tag offset?, size, align, rows)`
  let layout ← (if lb == 0 then pure none
    else if lb == 1 then do
      let enc ← u8
      let off ← (if enc == 0 then do let o ← v64; pure (some o)
        else if enc == 1 then do
          let _ ← v32; let _ ← v32; let _ ← v32; let _ ← leN 16; let _ ← v64
          let nt ← u8
          let _ ← tagRepr nt
          pure none
        else if enc == 2 && 37 ≤ v then pure none
        else if enc == 3 && 65 ≤ v then do let _ ← v32; pure none
        else bad "invalid tag" : P (Option Nat))
      let size ← v64
      let align ← v64
      let rows ← counted (counted v64)
      pure (some (off, size, align, rows))
    else bad "invalid tag" : P (Option (Option Nat × Nat × Nat × List (List Nat))))
  if 58 ≤ v then absent "enum.origin" else pure ()
  if nd == 0 && repr.isNone && layout.isNone then do
    if vs.length == 0 || 256 < vs.length then unsup "enum.tag_width"
    if vs.any (fun var => var.fields.any (fun t => !isScalarTy t || t.beq .ptr)) then
      unsup "enum.payload"
    pure { id := id, variants := vs, discs := (List.range vs.length).map (fun (i : Nat) => (i : Int)),
           tag := .u8 }
  else do
    if vs.length == 0 then unsup "enum.tag_width"
    if vs.any (fun var => !var.fields.isEmpty) then unsup "enum.payload"
    match effDiscs ds vs.length 0 [] with
    | none => unsup "enum.discriminants"
    | some discs =>
      match canonTag repr discs with
      | none => unsup "enum.tag_width"
      | some t =>
        match layout with
        | none => pure { id := id, variants := vs, discs := discs, tag := t }
        | some (some 0, size, align, rows) =>
          if size == tagBytes t && align == tagBytes t && rows.length == vs.length &&
              rows.all (·.isEmpty) then
            pure { id := id, variants := vs, discs := discs, tag := t }
          else unsup "enum.layout"
        | some _ => unsup "enum.layout"

/-- The scalar binding records accompanying a formula are bookkeeping only.
    They do not bind the execution environment or supply an assumption. Keep
    unsupported sorts/places refused instead of guessing their wire shape. -/
def scalarClauseBindingMetadata : P Unit := do
  strId
  let sort ← u8
  if sort == 0 then pure ()
  else if sort == 2 then do
    let width ← v32
    if width == 8 || width == 16 || width == 32 || width == 64 then pure ()
    else unsup "obligation.binding_width"
  else if sort ≤ 6 then unsup "obligation.binding_sort"
  else bad "invalid ClauseSort tag"
  let place ← u8
  if place == 0 || place == 1 then do let _ ← v32; pure ()
  else if place ≤ 5 || ((place == 6 || place == 7) && 46 ≤ (← version)) ||
      ((place == 8 || place == 9) && 59 ≤ (← version)) ||
      (place == 10 && 62 ≤ (← version)) then unsup "obligation.binding_place"
  else bad "invalid ClausePlace tag"

/-- A producer's formula is recorded text, never an execution premise. Read
    the exact schema/payload, optional strings and supported scalar binding
    records without interpreting the formula or granting proof authority. -/
def proofFormulaMetadata : P Unit := do
  strId
  strId
  let optString : P Unit := do
    let tag ← u8
    if tag == 0 then pure () else if tag == 1 then strId else bad "invalid tag"
  optString
  optString
  if 41 ≤ (← version) then do
    let _ ← counted scalarClauseBindingMetadata
    pure ()
  else pure ()

/-- `read_proof_obligation`: producer bookkeeping is decoded and ignored.
    No status, formula or annotation grants a semantic or proof premise. -/
def proofObligation : P Unit := do
  let v ← version
  let _ ← v32
  let kt ← u8
  if kt ≤ 12 then pure ()
  else if (kt == 13 || kt == 14) && 41 ≤ v then pure ()
  else if kt == 15 && 41 ≤ v then do strId; strId
  else bad "invalid ObligationKind tag"
  let st ← u8
  if st ≤ 4 then pure () else bad "invalid ProofStatus tag"
  strId
  let fm ← u8
  if fm == 0 then pure () else if fm == 1 then proofFormulaMetadata else bad "invalid tag"
  let fn ← u8
  if fn == 0 then pure () else if fn == 1 then do let _ ← v32; pure () else bad "invalid tag"
  let src ← u8
  if src == 0 then pure ()
  else if src == 1 then do
    strId
    strId
    let rg ← u8
    if rg == 0 then pure ()
    else if rg == 1 then do let _ ← rep 5 v32; pure ()
    else bad "invalid tag"
    let pb ← u8
    if pb == 0 then pure ()
    else if pb == 1 then do
      strId
      let alg ← u8
      if alg ≤ 1 then do let _ ← rep 32 u8; pure () else bad "invalid tag"
    else bad "invalid tag"
  else bad "invalid tag"
  let site ← u8
  if site == 0 then pure () else if site == 1 then do let _ ← rep 3 v32; pure () else bad "invalid tag"
  if 46 ≤ v then do
    let sp ← u8
    if sp == 0 then pure () else if sp == 1 then do strId; strId else bad "invalid tag"
  else pure ()

/-- One blob table row: the 32 digest bytes, then the counted bytes. -/
def blobEntry : P (List Nat × List Nat) := do
  let d ← rep 32 u8
  let n ← checkedLen
  let bytes ← rep n u8
  pure (d, bytes)

/-- The rows strictly ascend by digest (`blob_table_order_refusal`), so each
    digest is listed once. -/
def blobsAscending : List (List Nat × List Nat) → Bool
  | a :: b :: rest => bytesLt a.1 b.1 && blobsAscending (b :: rest)
  | _ => true

/-- A section that must be empty in the fragment. -/
def emptySection (feature : String) : P Unit := do
  let n ← checkedLen
  if n == 0 then pure () else unsup feature

def moduleBody : P Module := do
  let v ← version
  strId
  let fts ← counted funcTy
  let ss ← counted flatStructDef
  let es ← counted enumDef
  emptySection "records"
  emptySection "closure_types"
  emptySection "globals"
  let _ ← counted scalarMetadataType
  let fs ← counted func
  let _ ← counted proofObligation
  emptySection "proof_certificates"
  let target ← targetInfo
  let _ ← counted strId
  emptySection "obligation_diagnostics"
  emptySection "spec_modules"
  emptySection "universes"
  emptySection "predicates"
  if 41 ≤ v then do
    let _ ← counted strId
    emptySection "imports"
  else pure ()
  if 42 ≤ v then emptySection "tuple_layouts" else pure ()
  if 55 ≤ v then emptySection "drop_glue" else pure ()
  if 58 ≤ v then emptySection "closure_layouts" else pure ()
  let blobs ← (if 70 ≤ v then counted blobEntry else pure [])
  if !(blobsAscending blobs) then bad "the blob table is out of canonical order"
  let r ← remaining
  if r != 0 then bad "trailing bytes after canonical module payload"
  pure { funcTys := fts, structs := ss, enums := es, functions := fs, target := target,
         blobs := blobs }

/-- `TRUST_IR` -/
def magic : List Nat := [84, 82, 85, 83, 84, 95, 73, 82]

/-- Decode a module blob. -/
def decode (bs : List Nat) : Except DErr Module :=
  if bs.take 8 != magic then .error (.malformed "invalid magic") else
  match u32 0 #[] (bs.drop 8) with
  | .err e => .error e
  | .ok ver rest =>
    if ver < 38 || 70 < ver then .error (.unsupported "wire_version")
    else
      match checkedLen ver #[] rest with
      | .err e => .error e
      | .ok n rest =>
        match rep n rawStr ver #[] rest with
        | .err e => .error e
        | .ok pool rest =>
          match moduleBody ver pool.toArray rest with
          | .err e => .error e
          | .ok m _ => .ok m

/-- Decode a blob and run function `fid` on `args`. -/
def runBlob (bs : List Nat) (fid : Nat) (args : List Val) (fuel depth : Nat) :
    Except DErr Out :=
  match decode bs with
  | .error e => .error e
  | .ok m => .ok (runFunction m fid args fuel depth)

end SemR

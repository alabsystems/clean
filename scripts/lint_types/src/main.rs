// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The TYPED scan of `scripts/check_lint_coverage.py`.
//!
//! This binary IS rustc (`rustc_driver`, from the pinned toolchain's
//! rustc-dev), run by cargo as a STANDALONE_GATED crate's
//! `RUSTC_WORKSPACE_WRAPPER` over the crate's own units, plus two rules read
//! off the THIR the compiler lowers every body to. It exits as rustc does, with
//! one error per refusal.
//!
//! THE RULE. A catch-all over a gated enum -- an enum of [`ENUM_CRATES`]
//! (trust-ir) or of the crate being compiled -- compiles unchanged when the enum
//! gains a variant, so code that must classify every variant would absorb one
//! nobody classified. In every pattern the compiler builds (the arms of a
//! `match`, a macro's `match` included; the pattern of an `if let`, a `while
//! let` and a `let` chain; a `let .. else`; a `let`; a parameter), a CATCH-ALL --
//! `_`, a binding, a field a struct or tuple pattern leaves out, a slice's rest
//! -- is refused wherever ANOTHER alternative of the same pattern set names a
//! gated variant at or below the catch-all's place. The failure branch of an
//! `if let` / `while let` / `let` chain / `let .. else` is such an alternative:
//! a catch-all at the top.
//!
//! What the syn scan it replaces decided by hand, the compiler decides here
//! (verifiers r10 and r10b measured each of these passing the syn scan):
//!
//! * which catch-all the wildcard lints read -- nothing is left to clippy; a
//!   whole-arm `_` is judged like any other (`EMPTY => .., _ =>` over a struct
//!   holding a gated enum; `SOME_A => .., None => .., _ =>` over an `Option`);
//! * what a name in a pattern is -- rustc resolved it: a constant is EXPANDED
//!   into the variants it denotes (`SOME_A => .., Some(_) =>`), a binding is a
//!   binding whatever its case (`Some(甲)`, `const lower_case`);
//! * which constructor a path names -- `Self { .. }`, `Self(..)` and a type
//!   alias are the type they resolve to;
//! * which field a position is -- a field is its index in its variant, a
//!   reference (implicit ones included) is a step, a slice element is counted
//!   from the start or from the end (one of each may be one element), and a
//!   rest stands for every element past the ones its pattern names.
//!
//! A constant the compiler keeps opaque (a type that is not plain data) tells
//! apart everything at and below its place. The one `match` exempt is the one a
//! builtin derive of core writes (`#[derive(PartialEq)]` on a crate enum): its
//! `_` arm follows a test that the discriminants are equal.
//!
//! THE SECOND RULE: A VARIANT TOLD APART BY VALUE (verifier r11v). A pattern is
//! one way to tell a variant apart; a comparison is another, and its other
//! outcome is a catch-all too: `if t == Ty::A { .. } else { .. }`,
//! `ts.contains(&Ty::A)`, `mem::discriminant(&t) == mem::discriminant(&Ty::A)`,
//! `same(t, Ty::A)`. A value NAMES a gated variant when it is built from one --
//! the variant's constructor (a tuple variant's passed as a function
//! included), a constant, static or inline constant of a type that can hold a
//! gated enum as data -- or is a value of a gated enum that reads no variable
//! (`Ty::default()`, `unit()`: one fixed variant), or a call of a gated crate's
//! function that reads no variable (`CallingConv::all()`, `Sig::default()`,
//! `CallingConv::iter()`: one fixed value, whose body this crate cannot
//! follow). The FLOW follows what a value is computed from, to a fixed point
//! over the whole crate:
//!
//! * within a body: a field, an index, a reference, an aggregate, a branch, a
//!   `break`, a variable a `let`, a pattern or an assignment binds, a
//!   closure's captures, parameters (from the other arguments of the call it
//!   is passed to) and result, and a call of another crate's function (std's
//!   containers, iterators and conversions, `mem::discriminant`), whose result
//!   carries every argument and whose writable arguments -- `&mut`, `&` to a
//!   type that is not `Freeze` (`Cell::set`), a place a call hands back into
//!   its receiver (`*cell.borrow_mut() = ..`) -- take the other arguments.
//!   What is written through an ALIAS is written into what it aliases: a
//!   binding that can write into what it was bound from (`let r = &mut v`, an
//!   `IterMut`, an `Rc<RefCell<..>>` clone), a closure's writable parameter
//!   (`v.iter_mut().for_each(|x| *x = Ty::A)`), a closure or function erased
//!   to a `dyn Fn` or coerced to a pointer (every such call may run it);
//! * through the crate's own functions (lane r11b), as through a body: a
//!   parameter takes what every call passes it -- a trait method's call is
//!   the impl the compiler resolves it to, or else every impl of it in this
//!   crate, and a call through a function pointer is every function of this
//!   crate coerced to one with as many parameters; a call's result, what the
//!   callee writes through a writable argument, and what it calls a closure of
//!   the caller with (`f(x)`, or by passing it on: `[..].iter().any(f)` in
//!   `fn apply<F: Fn(Ty) -> bool>(f: F)`, `inner(f)`) carry every variant the
//!   callee names there and what it hands on of THAT call's arguments (another
//!   call's reach only the parameters: [`Vals::resolved`]);
//! * through the crate's impls of OTHER crates' traits (lane r11b, landing
//!   round), which that crate or the compiler calls where no call of this crate
//!   shows it (`Display::fmt` from core's formatting, `Drop::drop`, `next` from
//!   `Take::next`): a parameter of such a method may carry any variant the
//!   crate names ([`Flow::called_from_outside`]; a comparison trait's impl is
//!   left out, each call of it being judged where it is made), and a call of
//!   another crate's function carries what the crate's impls of the traits its
//!   bounds hold on a type of the crate -- or on a type that may be any, a
//!   type parameter, a trait object, an `impl Trait` -- name in their results
//!   ([`Flow::reentries`]: `opt.unwrap_or_default()` runs `Default::default`,
//!   and a closure it is passed, `w.take(3).any(|u| ..)` or `it.any(|u| ..)`
//!   for `it: I: Iterator`, is called with what `next` returns).
//!
//! Only a value of a type that can hold a gated enum carries one, and a
//! comparison tells apart only variants of the enums its operands' types hold
//! (a `TargetInfo` built with `Endianness::Little` does not name a variant of
//! the `Ty` compared downstream of it) -- [`Held`]. A type that may hold ANY
//! value (verifier land-clean-r1) -- a type parameter, a trait object, an `impl
//! Trait`, a projection no concrete type resolves -- carries every variant it
//! is computed from, and a comparison of one tells apart any gated enum: a
//! generic body is judged for what its calls pass it (`a == b` in `fn same<T:
//! Tag>`, a trait's default method, a generic impl behind `dyn`). Another
//! crate's ADT holds what its type arguments hold and the gated enums its
//! fields name ([`keeps_gated`]); a trait object in its fields is out of model.
//! A function's value holds what it returns. Then:
//!
//! * a comparison -- a method of `PartialEq`, `PartialOrd` or `Ord`, by
//!   operator, by name or passed as a value (`fold(Ty::A, Ord::max)`,
//!   `sort_by(Ord::cmp)`) -- with an operand that names a gated variant is
//!   refused; so is a call to a function whose bounds compare a type that can
//!   hold a gated enum -- its own (`contains`, `starts_with`, `strip_prefix`,
//!   `binary_search`, a map's `get`, a generic `fn same<T: PartialEq>`; for a
//!   function whose body is not followed, a bound whose supertrait compares),
//!   its impl's (`HashSet::insert`, `HashMap::entry`, `Vec::dedup`), or those
//!   of the impl a trait method resolves to (`map[&k]`) -- with an argument
//!   that names one. A comparison taken as a value that no call is passed as
//!   itself (kept, or coerced to a pointer) is refused, not judged;
//! * a gated enum cast to a number (`t as u32`, `Ty::A as u8`) is refused: the
//!   number stands for every variant, present and future. It is read off the
//!   source and its type-check, since the THIR of `Enum::Variant as u8` is
//!   already the number.
//!
//! Two values neither of which names a variant (`a == b`, `ts.contains(&t)`)
//! agree or differ; that tells no variant apart, and passes. The comparisons
//! the core's `assert_eq!` / `assert_ne!` write (by their diagnostic items) are
//! exempt -- their other outcome is a panic -- and so are those a builtin
//! derive writes (field by field, under one variant).
//!
//! FAIL-CLOSED. Every body the crate declares must reach the scan (after the
//! analysis, a body no pass lowered is lowered then); a pattern the compiler's
//! own THIR walk reaches that this scan did not read, and a pattern shape it
//! does not model, is refused, not judged; every THIR expression kind is
//! named in the flow, so one the compiler adds fails to compile here.
//! `matches!` over rustc's own enums is not used here: the three wildcard
//! lints are forbidden over this crate too.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::process::ExitCode;
use std::sync::{Mutex, OnceLock, PoisonError};
use std::thread::ThreadId;

use rustc_abi::{FieldIdx, VariantIdx, FIRST_VARIANT};
use rustc_data_structures::steal::Steal;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::{CtorOf, DefKind};
use rustc_hir::HirId;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::thir::visit::{self, Visitor};
use rustc_middle::thir::{
    AdtExprBase, Expr, ExprId, ExprKind, FieldPat, Pat, PatKind, StmtKind, Thir,
};
use rustc_middle::ty::{self, AdtDef, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::hygiene::{ExpnKind, MacroKind};
use rustc_span::{sym, ErrorGuaranteed, Span, Symbol};

/// The crates whose enums the rule holds a pattern to, beside the crate being
/// compiled.
const ENUM_CRATES: &[&str] = &["trust_ir"];

/// How many new types one search of [`Holds`] (or of
/// [`Flow::mutable_inside`]) walks before it holds that the type may hold any
/// gated enum (or a `&mut`). Measured on this crate's own scan (lane refix1):
/// a compiler's `TyCtxt` reaches 4,822 types, a `rustc_interface::Config`
/// more than 200,000 (a generic type's fields instantiate new types).
const HELD_LIMIT: usize = 50_000;

/// The variable whose value the scan records in each unit's dep-info, so a
/// fresh value makes cargo re-run the crate's own units -- and only those --
/// through this binary (clippy's `CLIPPY_ARGS`, the same mechanism).
const RUN_VAR: &str = "CLEAN_LINT_TYPES_RUN";

/// The needle every rule refusal carries, the second rule's included.
const CATCH_ALL: &str = "a catch-all over a gated enum";

type ThirBody<'tcx> = Result<(&'tcx Steal<Thir<'tcx>>, ExprId), ErrorGuaranteed>;
type ThirBodyFn = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> ThirBody<'tcx>;

/// The compiler's own `thir_body`, which [`thir_body`] wraps.
static ORIGINAL: OnceLock<ThirBodyFn> = OnceLock::new();

/// What the scan of each compilation found, by the thread compiling it. A
/// query provider is a plain `fn`, so it reports here, and the driver takes it
/// after the analysis: the compiler runs both on its one thread. A provider
/// run on another thread (a parallel front end) leaves its body out of the
/// compilation's `scanned`, and every such body is refused.
static FOUND: Mutex<Vec<(ThreadId, Found)>> = Mutex::new(Vec::new());

struct Refusal {
    span: Span,
    why: String,
    told: Option<Span>,
}

struct Found {
    /// The `local_def_index` of every body scanned.
    scanned: BTreeSet<u32>,
    refused: Vec<Refusal>,
    /// The flow of named variants through every body scanned, resolved once
    /// the analysis is over (a closure's body and the body it is written in
    /// are scanned in either order).
    edges: Edges,
    patterns: usize,
    sets: usize,
    derived: usize,
    /// What [`Holds`] found of every type with no parameter it asked about,
    /// by the address of its interned kind (unique for the compilation): the
    /// gated enums it holds, and whether it may hold any. The bodies share
    /// it.
    held_enums: HashMap<(usize, bool), BTreeSet<Enum>>,
    held_hidden: HashMap<usize, bool>,
    /// How many searches reached [`HELD_LIMIT`].
    capped: usize,
    /// [`keeps_gated`] of each ADT of another crate asked about.
    keeps: HashMap<DefId, bool>,
}

impl Found {
    fn new() -> Self {
        Self {
            scanned: BTreeSet::new(),
            refused: Vec::new(),
            edges: Edges::new(),
            patterns: 0,
            sets: 0,
            derived: 0,
            held_enums: HashMap::new(),
            held_hidden: HashMap::new(),
            capped: 0,
            keeps: HashMap::new(),
        }
    }
}

fn found<R>(each: impl FnOnce(&mut Found) -> R) -> R {
    let me = std::thread::current().id();
    let mut all = FOUND.lock().unwrap_or_else(PoisonError::into_inner);
    let at = all.iter().position(|(id, _)| *id == me).unwrap_or_else(|| {
        all.push((me, Found::new()));
        all.len() - 1
    });
    each(&mut all[at].1)
}

/// This thread's compilation's findings, taken.
fn take_found() -> Found {
    let me = std::thread::current().id();
    let mut all = FOUND.lock().unwrap_or_else(PoisonError::into_inner);
    let at = all.iter().position(|(id, _)| *id == me);
    at.map_or_else(Found::new, |at| all.swap_remove(at).1)
}

/// The `thir_body` provider: the compiler's, then the scan of what it built.
/// Every body the compilation lowers passes here exactly once (the query is
/// cached), before building its MIR steals it.
fn thir_body(tcx: TyCtxt<'_>, def: LocalDefId) -> ThirBody<'_> {
    let Some(original) = ORIGINAL.get() else {
        tcx.dcx()
            .fatal("lint-types: the compiler's `thir_body` provider was never installed");
    };
    let built = original(tcx, def);
    if let Ok((thir, root)) = &built {
        scan_body(tcx, def, &thir.borrow(), *root);
    }
    found(|found| found.scanned.insert(def.local_def_index.as_u32()));
    built
}

// ── THE RULE ────────────────────────────────────────────────────────────────

/// One step down from a pattern's place: a field of a variant (a struct or a
/// tuple is variant 0), a dereference, an element of a slice or an array
/// counted from its start or (`from_end`) its end, or the elements a rest
/// (`..`) stands for -- every one at least `start` places from the start and
/// `end` from the end.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Step {
    Field(VariantIdx, FieldIdx),
    Deref,
    Elem { index: usize, from_end: bool },
    Rest { start: usize, end: usize },
}

/// Whether two steps at one place may reach the same value. An element counted
/// from the start and one counted from the end may be one element (some
/// length makes them one).
fn overlap(a: Step, b: Step) -> bool {
    match (a, b) {
        (Step::Field(v, f), Step::Field(w, g)) => v == w && f == g,
        (
            Step::Elem {
                index: i,
                from_end: e,
            },
            Step::Elem {
                index: j,
                from_end: f,
            },
        ) => e != f || i == j,
        (Step::Rest { start, end }, Step::Elem { index, from_end })
        | (Step::Elem { index, from_end }, Step::Rest { start, end }) => {
            index >= if from_end { end } else { start }
        }
        (Step::Deref, Step::Deref) | (Step::Rest { .. }, Step::Rest { .. }) => true,
        // Two kinds of step at one place: the types rule it out, so the model
        // is wrong if it happens -- and then they may meet.
        (Step::Field(..), Step::Deref | Step::Elem { .. } | Step::Rest { .. })
        | (Step::Deref, Step::Field(..) | Step::Elem { .. } | Step::Rest { .. })
        | (Step::Elem { .. } | Step::Rest { .. }, Step::Field(..) | Step::Deref) => true,
    }
}

/// Whether a place `pos` may lie at or below `prefix`.
fn under(prefix: &[Step], pos: &[Step]) -> bool {
    prefix.len() <= pos.len() && prefix.iter().zip(pos).all(|(a, b)| overlap(*a, *b))
}

/// A place in one alternative of a pattern set: where a catch-all stands, or
/// where a gated variant (or an opaque constant) is told apart.
struct Site {
    alt: usize,
    pos: Vec<Step>,
    span: Span,
    what: String,
    /// An opaque constant: it tells apart everything at and below `pos`.
    deep: bool,
}

/// The alternatives of one pattern set -- the arms of a `match`, or one
/// pattern and, for a refutable `let`, its failure branch.
struct Alts<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    next_alt: usize,
    tells: Vec<Site>,
    catches: Vec<Site>,
    unmodeled: Vec<(Span, String)>,
    read: &'a mut BTreeSet<usize>,
}

fn down(pos: &[Step], step: Step) -> Vec<Step> {
    let mut next = pos.to_vec();
    next.push(step);
    next
}

/// Whether an ADT of a crate that is neither this one nor gated may keep a
/// gated enum in its own fields -- one of them names a gated enum, or an ADT of
/// another crate that may (a crate between this one and trust-ir). Any other
/// such ADT holds one only in what its type arguments are (`Vec<Ty>`,
/// `Box<dyn Check>`), or in a trait object of its own that a value was erased
/// into (an `io::Error`'s payload, a compiler's `dyn Any`), which is out of
/// model: its fields are not walked (a compiler's own `TyCtxt` reaches tens of
/// thousands of types, and a trait object among them).
fn keeps_gated(tcx: TyCtxt<'_>, root: DefId) -> bool {
    if let Some(known) = found(|found| found.keeps.get(&root).copied()) {
        return known;
    }
    let mut seen = HashSet::from([root]);
    let mut todo = vec![root];
    let mut keeps = false;
    'search: while let Some(def) = todo.pop() {
        if found(|found| found.keeps.get(&def).copied()) == Some(true) {
            keeps = true;
            break;
        }
        for field in tcx.adt_def(def).all_fields() {
            let written = tcx
                .type_of(field.did)
                .instantiate_identity()
                .skip_normalization();
            for arg in written.walk() {
                let Some(ty::Adt(adt, _)) = arg.as_type().map(|inner| inner.kind()) else {
                    continue;
                };
                if gated(tcx, *adt) {
                    keeps = true;
                    break 'search;
                }
                if seen.insert(adt.did()) {
                    todo.push(adt.did());
                }
            }
        }
    }
    // What it reaches keeps none, if it keeps none.
    found(|found| {
        if keeps {
            found.keeps.insert(root, true);
        } else {
            found.keeps.extend(seen.into_iter().map(|def| (def, false)));
        }
    });
    keeps
}

/// A gated enum: one of [`ENUM_CRATES`], or the crate's own.
fn gated(tcx: TyCtxt<'_>, adt: AdtDef<'_>) -> bool {
    let did = adt.did();
    adt.is_enum() && (did.is_local() || ENUM_CRATES.contains(&tcx.crate_name(did.krate).as_str()))
}

/// Plain data: what a constant of this type can tell apart is no variant.
fn plain(ty: Ty<'_>) -> bool {
    if ty.is_bool() || ty.is_char() || ty.is_integral() || ty.is_floating_point() || ty.is_str() {
        return true;
    }
    if let ty::Ref(_, inner, _) | ty::Array(inner, _) | ty::Slice(inner) = ty.kind() {
        return plain(*inner);
    }
    if let ty::Tuple(elems) = ty.kind() {
        return elems.iter().all(plain);
    }
    false
}

impl<'tcx> Alts<'_, 'tcx> {
    fn fresh(&mut self) -> usize {
        self.next_alt += 1;
        self.next_alt
    }

    fn site(pos: &[Step], alt: usize, span: Span, what: String, deep: bool) -> Site {
        Site {
            alt,
            pos: pos.to_vec(),
            span,
            what,
            deep,
        }
    }

    fn catch(&mut self, pos: &[Step], alt: usize, span: Span, what: String) {
        self.catches.push(Self::site(pos, alt, span, what, false));
    }

    fn tell(
        &mut self,
        adt: AdtDef<'tcx>,
        variant: VariantIdx,
        pos: &[Step],
        alt: usize,
        span: Span,
    ) {
        if gated(self.tcx, adt) {
            let path = self.tcx.def_path_str(adt.variant(variant).def_id);
            self.tells
                .push(Self::site(pos, alt, span, format!("`{path}`"), false));
        }
    }

    fn walk(&mut self, pat: &Pat<'tcx>, pos: &[Step], alt: usize) {
        self.read.insert(std::ptr::from_ref(pat) as usize);
        match &pat.kind {
            PatKind::Wild => self.catch(pos, alt, pat.span, "`_`".to_string()),
            PatKind::Missing => self.catch(pos, alt, pat.span, "a missing pattern".to_string()),
            PatKind::Binding {
                name, subpattern, ..
            } => match subpattern {
                Some(sub) => self.walk(sub, pos, alt),
                None => self.catch(pos, alt, pat.span, format!("the binding `{name}`")),
            },
            PatKind::Variant {
                adt_def,
                variant_index,
                subpatterns,
                ..
            } => {
                self.tell(*adt_def, *variant_index, pos, alt, pat.span);
                let fields = adt_def.variant(*variant_index).fields.len();
                self.fields(subpatterns, fields, *variant_index, pos, alt, pat.span);
            }
            PatKind::Leaf { subpatterns } => {
                if let ty::Adt(adt, _) = pat.ty.kind() {
                    if adt.is_enum() && adt.variants().len() != 1 {
                        let why = format!("a leaf pattern over the enum `{}`", pat.ty);
                        self.unmodeled.push((pat.span, why));
                        return;
                    }
                    self.tell(*adt, FIRST_VARIANT, pos, alt, pat.span);
                    let fields = adt.variant(FIRST_VARIANT).fields.len();
                    self.fields(subpatterns, fields, FIRST_VARIANT, pos, alt, pat.span);
                } else if let ty::Tuple(elems) = pat.ty.kind() {
                    self.fields(subpatterns, elems.len(), FIRST_VARIANT, pos, alt, pat.span);
                } else {
                    let why = format!("a field pattern over `{}`", pat.ty);
                    self.unmodeled.push((pat.span, why));
                }
            }
            PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
                self.walk(subpattern, &down(pos, Step::Deref), alt);
            }
            PatKind::Constant { .. } => {
                if !plain(pat.ty) {
                    let what = format!("a constant of type `{}`", pat.ty);
                    self.tells.push(Self::site(pos, alt, pat.span, what, true));
                }
            }
            PatKind::Slice {
                prefix,
                slice,
                suffix,
            }
            | PatKind::Array {
                prefix,
                slice,
                suffix,
            } => {
                for (index, sub) in prefix.iter().enumerate() {
                    let from_end = false;
                    self.walk(sub, &down(pos, Step::Elem { index, from_end }), alt);
                }
                for (index, sub) in suffix.iter().rev().enumerate() {
                    let from_end = true;
                    self.walk(sub, &down(pos, Step::Elem { index, from_end }), alt);
                }
                if let Some(rest) = slice {
                    let (start, end) = (prefix.len(), suffix.len());
                    self.walk(rest, &down(pos, Step::Rest { start, end }), alt);
                }
            }
            PatKind::Or { pats } => {
                for case in pats.iter() {
                    let case_alt = self.fresh();
                    self.walk(case, pos, case_alt);
                }
            }
            PatKind::Guard { subpattern, .. } => self.walk(subpattern, pos, alt),
            // A range tells apart numbers and chars only; `!` matches nothing;
            // an error pattern has already failed the compilation.
            PatKind::Range(_) | PatKind::Never | PatKind::Error(_) => {}
        }
    }

    /// The fields of one variant: each named one walked, each left out a
    /// catch-all at its place.
    fn fields(
        &mut self,
        subpatterns: &[FieldPat<'tcx>],
        count: usize,
        variant: VariantIdx,
        pos: &[Step],
        alt: usize,
        span: Span,
    ) {
        let mut named = vec![false; count];
        for field in subpatterns {
            let Some(seen) = named.get_mut(field.field.as_usize()) else {
                let why = format!("field {} of a variant with {count}", field.field.as_usize());
                self.unmodeled.push((field.pattern.span, why));
                continue;
            };
            *seen = true;
            let place = down(pos, Step::Field(variant, field.field));
            self.walk(&field.pattern, &place, alt);
        }
        for (index, seen) in named.iter().enumerate() {
            if !seen {
                let place = down(pos, Step::Field(variant, FieldIdx::from_usize(index)));
                self.catch(
                    &place,
                    alt,
                    span,
                    format!("field {index}, which this pattern leaves out"),
                );
            }
        }
    }

    /// Each catch-all that stands for what another alternative tells apart at
    /// or below its place -- or, for an opaque constant, anywhere along it.
    fn verdicts(self) -> Vec<Refusal> {
        let mut out = Vec::new();
        for catch in &self.catches {
            let told = self.tells.iter().find(|tell| {
                tell.alt != catch.alt
                    && (under(&catch.pos, &tell.pos) || tell.deep && under(&tell.pos, &catch.pos))
            });
            if let Some(tell) = told {
                out.push(Refusal {
                    span: catch.span,
                    why: format!(
                        "{} stands for what another alternative of this pattern tells apart at the same place ({}) -- {CATCH_ALL} compiles unchanged when the enum gains a variant; name the variants",
                        catch.what, tell.what
                    ),
                    told: Some(tell.span),
                });
            }
        }
        for (span, why) in self.unmodeled {
            out.push(Refusal {
                span,
                why: format!("a pattern this scan does not model ({why}) -- refused, not judged"),
                told: None,
            });
        }
        out
    }
}

/// Whether `span` was written by a builtin derive of core.
fn from_builtin_derive(tcx: TyCtxt<'_>, span: Span) -> bool {
    span.macro_backtrace().any(|expn| {
        let ExpnKind::Macro(MacroKind::Derive, _) = expn.kind else {
            return false;
        };
        expn.macro_def_id
            .is_some_and(|def| tcx.crate_name(def.krate).as_str() == "core")
    })
}

/// Reports every top-level pattern the compiler's own THIR walk reaches that
/// the scan did not read: a construct that binds a pattern somewhere this scan
/// does not look.
struct Unread<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    read: &'a BTreeSet<usize>,
    missed: Vec<Span>,
}

impl<'a, 'tcx> Visitor<'a, 'tcx> for Unread<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_pat(&mut self, pat: &'a Pat<'tcx>) {
        if !self.read.contains(&(std::ptr::from_ref(pat) as usize)) {
            self.missed.push(pat.span);
        }
        visit::walk_pat(self, pat);
    }
}

// ── THE SECOND RULE: a variant told apart by value ─────────────────────────

/// A variable, as the flow keys it: its `HirId` (the owner's def index and the
/// local id). A closure's capture is the variable it captures.
type Var = (u32, u32);

/// A parameter of a function of this crate: the function's def index and the
/// parameter's position (`self` is 0).
type Param = (u32, u32);

/// One call of a function of this crate: the calling body's def index and the
/// call's expression.
type Call = (u32, u32);

fn var_key(id: HirId) -> Var {
    (
        id.owner.def_id.local_def_index.as_u32(),
        id.local_id.as_u32(),
    )
}

fn def_key(def: LocalDefId) -> u32 {
    def.local_def_index.as_u32()
}

fn index_key(index: usize) -> u32 {
    u32::try_from(index).unwrap_or(u32::MAX)
}

/// Where a variant or constant is named, and which.
type Witness = (Span, String);

/// A gated enum, as the flow keys it: its `DefId`'s crate and index.
type Enum = (u32, u32);

fn enum_key(did: DefId) -> Enum {
    (did.krate.as_u32(), did.index.as_u32())
}

/// The named variants a value may carry, one witness per gated enum: a
/// comparison tells apart only variants of the enums its operands' types hold.
type Named = BTreeMap<Enum, Witness>;

/// What a value is computed from, as far as a named variant goes: the variants
/// and constants named in it, and what else the flow resolves -- the
/// variables, closure parameters and closure results it is computed from, the
/// parameters of the crate's functions it may be, the calls of them it may be
/// the result of, and the crate's functions it may be (passed as a value).
/// `mask` is the gated enums the value's type can hold (none: a type that may
/// hold any, or a union of values of different types): a variant of any other
/// enum is not in it, whatever it was computed from. `every` stands for every
/// variant the crate names, with this witness: a parameter another crate (or
/// the compiler) may pass any value, a fixed value whose type may hold any.
#[derive(Clone, Default)]
struct Src {
    named: Named,
    every: Option<Witness>,
    mask: Option<BTreeSet<Enum>>,
    vars: BTreeSet<Var>,
    closure_params: BTreeSet<u32>,
    closure_results: BTreeSet<u32>,
    /// What a closure writes through its parameters.
    closure_writes: BTreeSet<u32>,
    params: BTreeSet<Param>,
    calls: BTreeSet<Call>,
    fn_items: BTreeSet<u32>,
    /// What the function a parameter belongs to calls it with (a comparison
    /// passed to it as a value compares those).
    called_with: BTreeSet<Param>,
}

impl Src {
    /// A variant or constant of each of `enums`, named at `span`.
    fn named(enums: impl IntoIterator<Item = Enum>, span: Span, what: &str) -> Self {
        Self {
            named: enums
                .into_iter()
                .map(|enum_def| (enum_def, (span, what.to_string())))
                .collect(),
            ..Self::default()
        }
    }

    /// Every gated variant a fixed value of a type that holds `held` may be,
    /// named at `span`: those its type shows, and every one the crate names
    /// when it may hold any.
    fn fixed(held: &Held, span: Span, what: &str) -> Self {
        let mut out = Self::named(held.data.iter().copied(), span, what);
        if held.hidden {
            out.every = Some((span, what.to_string()));
        }
        out
    }

    fn join(&mut self, other: &Self) {
        if other.is_empty() {
            return;
        }
        if self.is_empty() {
            self.clone_from(other);
            return;
        }
        self.mask = match (&self.mask, &other.mask) {
            (Some(mine), Some(theirs)) => Some(mine.union(theirs).copied().collect()),
            (None, Some(_) | None) | (Some(_), None) => None,
        };
        for (enum_def, witness) in &other.named {
            self.named
                .entry(*enum_def)
                .or_insert_with(|| witness.clone());
        }
        if self.every.is_none() {
            self.every.clone_from(&other.every);
        }
        self.vars.extend(other.vars.iter().copied());
        self.closure_params
            .extend(other.closure_params.iter().copied());
        self.closure_results
            .extend(other.closure_results.iter().copied());
        self.closure_writes
            .extend(other.closure_writes.iter().copied());
        self.params.extend(other.params.iter().copied());
        self.calls.extend(other.calls.iter().copied());
        self.fn_items.extend(other.fn_items.iter().copied());
        self.called_with.extend(other.called_with.iter().copied());
    }

    fn is_empty(&self) -> bool {
        self.named.is_empty()
            && self.every.is_none()
            && self.vars.is_empty()
            && self.closure_params.is_empty()
            && self.closure_results.is_empty()
            && self.closure_writes.is_empty()
            && self.params.is_empty()
            && self.calls.is_empty()
            && self.fn_items.is_empty()
            && self.called_with.is_empty()
    }
}

/// A comparison the second rule judges once every body's flow is known: it
/// tells apart variants of `enums` -- of any gated enum, when `None`: its
/// operands' type may hold any (a comparison of a type parameter in a generic
/// body, which its calls instantiate with the concrete types).
struct Sink {
    span: Span,
    what: String,
    enums: Option<BTreeSet<Enum>>,
    src: Src,
}

/// A trait bound a call holds: the trait, the types it bounds, and whether it
/// is a where-clause ([`Flow::bounds`]).
type Bound<'tcx> = (DefId, Vec<Ty<'tcx>>, bool);

/// One call of a function of this crate: the one body the compiler resolved
/// it to, or every body of this crate implementing a trait method it could
/// not resolve.
struct CallSite {
    at: Call,
    callees: Vec<u32>,
    /// The callee is resolved: what it hands back of its arguments is read
    /// off its body. Otherwise the call's value already carries all of them.
    resolved: bool,
    /// What each argument is computed from, by position.
    args: Vec<Src>,
    /// Each argument the callee can write through, and the variable it is
    /// rooted at.
    writes: Vec<(u32, Var)>,
    /// Each argument that is a closure of this crate, which the callee may
    /// call back.
    closures: Vec<(u32, u32)>,
}

/// What one body's flow adds to the compilation's.
#[derive(Default)]
struct Edges {
    vars: Vec<(Var, Src)>,
    closure_params: Vec<(u32, Src)>,
    closure_results: Vec<(u32, Src)>,
    closure_writes: Vec<(u32, Src)>,
    /// What a call passes a parameter of a function of this crate.
    params: Vec<(Param, Src)>,
    /// What a function of this crate returns.
    results: Vec<(u32, Src)>,
    /// What a function of this crate leaves in what its parameter refers to (a
    /// `&mut`, or a `&` to a type that is not `Freeze`).
    writes: Vec<(Param, Src)>,
    calls: Vec<CallSite>,
    /// A call of a closure or function value (`f(x)`, through the `Fn`
    /// traits), or one passed to another crate's function with other
    /// arguments: what it is called with, by what the callee is.
    callbacks: Vec<(Src, Src)>,
    /// A function value passed to a parameter of a function of this crate:
    /// it is called with what that parameter is called with.
    forwards: Vec<(Src, Param)>,
    /// The functions of this crate taken as a value somewhere (`let p: fn(Ty)
    /// = same`), and how many parameters each has.
    reified: Vec<(u32, usize)>,
    /// What a call through a function pointer passes (`p(t, Ty::A)`), or what
    /// a callee it is passed to may call it with: every function taken as a
    /// value with that many parameters takes it, and every erased closure.
    pointer_calls: Vec<(usize, Vec<Src>)>,
    /// The closures of this crate coerced to a `dyn Fn` or a function pointer
    /// somewhere: which body a call through one runs is not known.
    erased: Vec<u32>,
    /// What a call of a `dyn Fn` passes: every erased closure takes it.
    erased_calls: Vec<Src>,
    sinks: Vec<Sink>,
    /// Every gated variant the crate names, one witness per enum: what a
    /// parameter another crate may pass any value can carry.
    named: Named,
}

impl Edges {
    const fn new() -> Self {
        Self {
            vars: Vec::new(),
            closure_params: Vec::new(),
            closure_results: Vec::new(),
            closure_writes: Vec::new(),
            params: Vec::new(),
            results: Vec::new(),
            writes: Vec::new(),
            calls: Vec::new(),
            callbacks: Vec::new(),
            forwards: Vec::new(),
            reified: Vec::new(),
            pointer_calls: Vec::new(),
            erased: Vec::new(),
            erased_calls: Vec::new(),
            sinks: Vec::new(),
            named: BTreeMap::new(),
        }
    }

    fn extend(&mut self, other: Self) {
        self.vars.extend(other.vars);
        self.closure_params.extend(other.closure_params);
        self.closure_results.extend(other.closure_results);
        self.closure_writes.extend(other.closure_writes);
        self.params.extend(other.params);
        self.results.extend(other.results);
        self.writes.extend(other.writes);
        self.calls.extend(other.calls);
        self.callbacks.extend(other.callbacks);
        self.forwards.extend(other.forwards);
        self.reified.extend(other.reified);
        self.pointer_calls.extend(other.pointer_calls);
        self.erased.extend(other.erased);
        self.erased_calls.extend(other.erased_calls);
        self.sinks.extend(other.sinks);
        for (enum_def, witness) in other.named {
            self.named.entry(enum_def).or_insert(witness);
        }
    }
}

/// The gated enums a type can hold a value of: those its structure shows
/// (`enums`), and whether it may hold ANY other (`hidden`).
///
/// A type parameter, a trait object, an `impl Trait`, a projection no concrete
/// type resolves and a coroutine are `hidden`: the value behind each may be of
/// any type, so a value of one carries every variant it is computed from, and
/// a comparison of one may tell apart a variant of any gated enum (verifier
/// land-clean-r1: an `impl Iterator<Item = Ty>` result, a `Vec<Box<dyn
/// Check>>` and a comparison of a type parameter each held nothing, and each
/// dropped the variants that flowed into it). What such a type SHOWS is still
/// in `enums` -- an `impl Trait`'s bounds (`Item = Ty`), a trait object's, the
/// gated enums written in a projection -- for naming a fixed value of a gated
/// crate ([`Flow::calls_gated_crate`]).
#[derive(Clone, Default)]
struct Held {
    enums: BTreeSet<Enum>,
    hidden: bool,
    /// Of `enums`, those a value of the type holds as data -- not only in
    /// what a function it is returns: what a constant of it stands for.
    data: BTreeSet<Enum>,
}

impl Held {
    /// The gated enums a value of the type can carry: `None`, any.
    fn mask(&self) -> Option<BTreeSet<Enum>> {
        (!self.hidden).then(|| self.enums.clone())
    }

    /// Whether the flow follows values of the type.
    fn carries(&self) -> bool {
        self.hidden || !self.enums.is_empty()
    }

    /// The gated enums written in a type (its own and its arguments', not its
    /// fields').
    fn insert_written(&mut self, tcx: TyCtxt<'_>, ty: Ty<'_>) {
        for arg in ty.walk() {
            if let Some(ty::Adt(adt, _)) = arg.as_type().map(|inner| inner.kind()) {
                if gated(tcx, *adt) {
                    self.enums.insert(enum_key(adt.did()));
                }
            }
        }
    }
}

/// [`Held`] of each type: the enum itself, what the fields and type arguments
/// of an ADT hold, what a closure's captures and result hold, what a function
/// item's or pointer's result holds (a variant's constructor, passed as a
/// function).
///
/// Only a field of an ADT of this crate can hide a value: a trait object or
/// an `impl Trait` in a field of another crate's ADT (an `io::Error`'s
/// payload, a compiler's own `dyn Any`) holds what a value was erased into it
/// through that crate's API, which is out of model -- what such an ADT holds
/// is what its type arguments hold (`Vec<Box<dyn Check>>` may hold any), and
/// the gated enums its fields name ([`keeps_gated`]).
struct Holds<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// The body's, for normalizing a field's type (`NonZero<u64>`'s field is
    /// `<u64 as ZeroablePrimitive>::NonZeroInner`, `TyKind`'s are the
    /// interner's associated types): unnormalized, each would be a projection,
    /// which may hold any.
    typing_env: ty::TypingEnv<'tcx>,
    memo: HashMap<Ty<'tcx>, Held>,
    /// By type and whether only data counts ([`Held::data`]).
    enums: HashMap<(Ty<'tcx>, bool), BTreeSet<Enum>>,
    hidden: HashMap<Ty<'tcx>, bool>,
}

/// One type held directly by another: whether a value hidden in it (a trait
/// object, an `impl Trait`, a type parameter) is hidden in the other, and
/// whether it is held as data (not only in what a function returns).
type Edge<'tcx> = (Ty<'tcx>, bool, bool);

impl<'tcx> Holds<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, def: LocalDefId) -> Self {
        Self {
            tcx,
            typing_env: ty::TypingEnv::non_body_analysis(tcx, def),
            memo: HashMap::new(),
            enums: HashMap::new(),
            hidden: HashMap::new(),
        }
    }

    /// [`Held`] of `ty`: every gated enum a type it reaches holds, and whether
    /// it reaches a hidden one. Each type is searched once for the
    /// compilation (the graph a compiler's own types reach, which this crate's
    /// own scan walks, is in the thousands); past [`HELD_LIMIT`] new types in
    /// one search, `ty` may hold any (a generic type's fields may instantiate
    /// new types without end).
    fn held(&mut self, ty: Ty<'tcx>) -> Held {
        if let Some(known) = self.memo.get(&ty) {
            return known.clone();
        }
        let root = self.tcx.erase_and_anonymize_regions(ty);
        let hidden = self.hidden_in(root);
        let held = match (self.enums_of(root, false), self.enums_of(root, true)) {
            (Some(enums), Some(data)) => Held {
                enums,
                hidden: hidden.unwrap_or(true),
                data,
            },
            (Some(_) | None, None) | (None, Some(_)) => Held {
                enums: BTreeSet::new(),
                hidden: true,
                data: BTreeSet::new(),
            },
        };
        self.memo.insert(ty, held.clone());
        held
    }

    /// Whether the flow follows values of this type: it holds a gated enum,
    /// or it may hold any.
    fn carries(&mut self, ty: Ty<'tcx>) -> bool {
        self.held(ty).carries()
    }

    fn mask(&mut self, ty: Ty<'tcx>) -> Option<BTreeSet<Enum>> {
        self.held(ty).mask()
    }

    fn known_enums(&mut self, ty: Ty<'tcx>, data: bool) -> Option<BTreeSet<Enum>> {
        if let Some(known) = self.enums.get(&(ty, data)) {
            return Some(known.clone());
        }
        let key = shared_key(ty)?;
        let known = found(|found| found.held_enums.get(&(key, data)).cloned())?;
        self.enums.insert((ty, data), known.clone());
        Some(known)
    }

    fn keep_enums(&mut self, ty: Ty<'tcx>, data: bool, enums: BTreeSet<Enum>) {
        if let Some(key) = shared_key(ty) {
            let shared = enums.clone();
            found(|found| found.held_enums.insert((key, data), shared));
        }
        self.enums.insert((ty, data), enums);
    }

    fn known_hidden(&mut self, ty: Ty<'tcx>) -> Option<bool> {
        if let Some(known) = self.hidden.get(&ty) {
            return Some(*known);
        }
        let key = shared_key(ty)?;
        let known = found(|found| found.held_hidden.get(&key).copied())?;
        self.hidden.insert(ty, known);
        Some(known)
    }

    fn keep_hidden(&mut self, ty: Ty<'tcx>, hidden: bool) {
        if let Some(key) = shared_key(ty) {
            found(|found| found.held_hidden.insert(key, hidden));
        }
        self.hidden.insert(ty, hidden);
    }

    /// The gated enums `root` holds (`data`: as data) -- Tarjan's search
    /// over those edges, iterative: each strongly connected component's types
    /// hold what any of them holds and what every type they reach holds.
    /// `None` past [`HELD_LIMIT`] new types.
    fn enums_of(&mut self, root: Ty<'tcx>, data: bool) -> Option<BTreeSet<Enum>> {
        if let Some(known) = self.known_enums(root, data) {
            return Some(known);
        }
        let mut search = Search::default();
        // Each type being visited, and the next of its children to visit.
        let mut frames: Vec<(Ty<'tcx>, usize)> = Vec::new();
        self.enter(root, data, &mut search);
        frames.push((root, 0));
        while let Some((ty, next)) = frames.last_mut() {
            let ty = *ty;
            let child = search
                .children
                .get(&ty)
                .and_then(|all| all.get(*next))
                .copied();
            *next += 1;
            if let Some(child) = child {
                if self.known_enums(child, data).is_some() {
                    continue;
                }
                if let Some(order) = search.order.get(&child).copied() {
                    if search.on_stack.contains(&child) {
                        search.lower(ty, order);
                    }
                    continue;
                }
                if search.order.len() >= HELD_LIMIT {
                    found(|found| found.capped += 1);
                    return None;
                }
                self.enter(child, data, &mut search);
                frames.push((child, 0));
                continue;
            }
            frames.pop();
            let low = search.low.get(&ty).copied().unwrap_or(0);
            if let Some((parent, _)) = frames.last() {
                search.lower(*parent, low);
            }
            if Some(low) != search.order.get(&ty).copied() {
                continue;
            }
            // `ty` roots a component: pop it, and give every member what the
            // component holds and what it reaches outside itself holds.
            let mut members = Vec::new();
            while let Some(member) = search.stack.pop() {
                search.on_stack.remove(&member);
                members.push(member);
                if member == ty {
                    break;
                }
            }
            let mut enums = BTreeSet::new();
            for member in &members {
                enums.extend(search.own.remove(member).unwrap_or_default());
                for reached in search.children.get(member).cloned().unwrap_or_default() {
                    enums.extend(self.known_enums(reached, data).unwrap_or_default());
                }
            }
            for member in members {
                self.keep_enums(member, data, enums.clone());
            }
        }
        self.known_enums(root, data)
    }

    fn enter(&self, ty: Ty<'tcx>, data: bool, search: &mut Search<'tcx>) {
        let (own, edges) = self.step(ty);
        let at = search.order.len();
        search.order.insert(ty, at);
        search.low.insert(ty, at);
        search.own.insert(ty, own.enums);
        search.stack.push(ty);
        search.on_stack.insert(ty);
        let children = edges
            .into_iter()
            .filter(|(_, _, held_as_data)| *held_as_data || !data)
            .map(|(child, _, _)| child)
            .collect();
        search.children.insert(ty, children);
    }

    /// Whether `root` reaches, along the edges a value may be hidden through,
    /// a type that hides one. A search that finds none has walked all that
    /// every type it visited reaches: none of them hides one. `None` past
    /// [`HELD_LIMIT`] new types.
    fn hidden_in(&mut self, root: Ty<'tcx>) -> Option<bool> {
        if let Some(known) = self.known_hidden(root) {
            return Some(known);
        }
        let mut seen = HashSet::from([root]);
        let mut todo = vec![root];
        while let Some(ty) = todo.pop() {
            let (own, edges) = self.step(ty);
            if own.hidden {
                self.keep_hidden(root, true);
                return Some(true);
            }
            for (child, hides, _) in edges {
                if !hides {
                    continue;
                }
                match self.known_hidden(child) {
                    Some(true) => {
                        self.keep_hidden(root, true);
                        return Some(true);
                    }
                    Some(false) => {}
                    None => {
                        if seen.len() >= HELD_LIMIT {
                            found(|found| found.capped += 1);
                            return None;
                        }
                        if seen.insert(child) {
                            todo.push(child);
                        }
                    }
                }
            }
        }
        for ty in seen {
            self.keep_hidden(ty, false);
        }
        Some(false)
    }

    /// What one type holds itself, and the types it holds directly. Every
    /// kind is named, so one the compiler adds fails to compile here.
    fn step(&self, ty: Ty<'tcx>) -> (Held, Vec<Edge<'tcx>>) {
        let tcx = self.tcx;
        let mut own = Held::default();
        let mut edges: Vec<Edge<'tcx>> = Vec::new();
        let hold = |edges: &mut Vec<Edge<'tcx>>, child: Ty<'tcx>| {
            edges.push((tcx.erase_and_anonymize_regions(child), true, true));
        };
        // What a function returns, which a value of it does not hold as data.
        let returns = |edges: &mut Vec<Edge<'tcx>>, output: Ty<'tcx>| {
            edges.push((tcx.erase_and_anonymize_regions(output), true, false));
        };
        match ty.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Foreign(_) => {}
            &ty::Adt(adt, args) => {
                if gated(tcx, adt) {
                    own.enums.insert(enum_key(adt.did()));
                }
                for arg in args.types() {
                    hold(&mut edges, arg);
                }
                let did = adt.did();
                let fields = did.is_local()
                    || ENUM_CRATES.contains(&tcx.crate_name(did.krate).as_str())
                    || keeps_gated(tcx, did);
                if fields {
                    for field in adt.all_fields() {
                        let field = field.ty(tcx, args);
                        let normal = tcx.try_normalize_erasing_regions(self.typing_env, field);
                        let field = normal.unwrap_or_else(|_| field.skip_normalization());
                        let field = tcx.erase_and_anonymize_regions(field);
                        edges.push((field, did.is_local(), true));
                    }
                }
            }
            ty::Ref(_, inner, _)
            | ty::RawPtr(inner, _)
            | ty::Array(inner, _)
            | ty::Slice(inner)
            | ty::Pat(inner, _) => hold(&mut edges, *inner),
            ty::Tuple(elems) => {
                for elem in *elems {
                    hold(&mut edges, elem);
                }
            }
            ty::Closure(_, args) => {
                let closure = args.as_closure();
                for up in closure.upvar_tys() {
                    hold(&mut edges, up);
                }
                let sig = tcx.instantiate_bound_regions_with_erased(closure.sig());
                returns(&mut edges, sig.output());
            }
            ty::FnDef(def, args) => {
                let sig = tcx
                    .fn_sig(*def)
                    .instantiate(tcx, tcx.instantiate_bound_regions_with_erased(*args))
                    .skip_normalization();
                returns(
                    &mut edges,
                    tcx.instantiate_bound_regions_with_erased(sig).output(),
                );
            }
            // What a call through it returns.
            ty::FnPtr(sig_tys, _) => {
                let sig_tys = tcx.instantiate_bound_regions_with_erased(*sig_tys);
                returns(&mut edges, sig_tys.output());
            }
            // An `impl Trait`: what its arguments and its bounds show. Any
            // other alias is a projection no concrete type resolves: the gated
            // enums written in it.
            ty::Alias(_, alias) => {
                own.hidden = true;
                let ty::Opaque { def_id } = alias.kind else {
                    own.insert_written(tcx, ty);
                    return (own, edges);
                };
                for arg in alias.args.types() {
                    hold(&mut edges, arg);
                }
                let bounds = tcx
                    .explicit_item_bounds(def_id)
                    .iter_instantiated_copied(tcx, alias.args);
                for bound in bounds {
                    let (clause, _) = bound.skip_normalization();
                    if let Some(projection) = clause.as_projection_clause() {
                        if let Some(term) = projection.skip_binder().term.as_type() {
                            hold(&mut edges, term);
                        }
                    } else if let Some(pred) = clause.as_trait_clause() {
                        for arg in pred.skip_binder().trait_ref.args.types().skip(1) {
                            hold(&mut edges, arg);
                        }
                    }
                }
            }
            // A trait object: what its bounds show (`dyn Iterator<Item =
            // Key>`).
            ty::Dynamic(..) => {
                own.hidden = true;
                for inner in ty.walk().skip(1).filter_map(|arg| arg.as_type()) {
                    hold(&mut edges, inner);
                }
            }
            // A type parameter, a coroutine's state: the gated enums written
            // in it.
            ty::Param(_)
            | ty::Coroutine(..)
            | ty::CoroutineClosure(..)
            | ty::CoroutineWitness(..)
            | ty::UnsafeBinder(_)
            | ty::Bound(..)
            | ty::Placeholder(_)
            | ty::Infer(_)
            | ty::Error(_) => {
                own.hidden = true;
                own.insert_written(tcx, ty);
            }
        }
        (own, edges)
    }
}

/// The compilation-wide key of a type with no parameter: the address of its
/// interned kind (unique for the compilation).
fn shared_key(ty: Ty<'_>) -> Option<usize> {
    (!ty.has_param()).then(|| std::ptr::from_ref(ty.kind()) as usize)
}

/// One search of [`Holds::enums_of`]: the order each type was entered in, the
/// lowest order it reaches, the gated enums it is itself, the types it holds
/// directly, and the component stack.
#[derive(Default)]
struct Search<'tcx> {
    order: HashMap<Ty<'tcx>, usize>,
    low: HashMap<Ty<'tcx>, usize>,
    own: HashMap<Ty<'tcx>, BTreeSet<Enum>>,
    children: HashMap<Ty<'tcx>, Vec<Ty<'tcx>>>,
    stack: Vec<Ty<'tcx>>,
    on_stack: HashSet<Ty<'tcx>>,
}

impl<'tcx> Search<'tcx> {
    fn lower(&mut self, ty: Ty<'tcx>, to: usize) {
        if let Some(low) = self.low.get_mut(&ty) {
            *low = (*low).min(to);
        }
    }
}

fn matches_adt_gated(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    if let ty::Adt(adt, _) = ty.kind() {
        return gated(tcx, *adt);
    }
    false
}

/// The traits whose methods, and whose bounds on a function, compare values.
fn comparison_trait(tcx: TyCtxt<'_>, did: DefId) -> bool {
    let items = tcx.lang_items();
    items.eq_trait() == Some(did)
        || items.partial_ord_trait() == Some(did)
        || tcx.is_diagnostic_item(sym::Ord, did)
        || tcx.is_diagnostic_item(sym::Eq, did)
}

/// Whether `span` is the comparison core's `assert_eq!` or `assert_ne!`
/// writes (the macros themselves, by their diagnostic items): its other
/// outcome is a panic, not a default for other variants.
fn from_assertion(tcx: TyCtxt<'_>, span: Span) -> bool {
    span.ctxt()
        .outer_expn_data()
        .macro_def_id
        .is_some_and(|def| {
            tcx.is_diagnostic_item(sym::assert_eq_macro, def)
                || tcx.is_diagnostic_item(sym::assert_ne_macro, def)
        })
}

/// The closures of this crate a type holds (`{closure}`, `Box<{closure}>`, a
/// structure generic over one).
fn closures_of(ty: Ty<'_>) -> Vec<LocalDefId> {
    let mut out = Vec::new();
    for arg in ty.walk() {
        if let Some(ty::Closure(closure, _)) = arg.as_type().map(|inner| inner.kind()) {
            if let Some(local) = closure.as_local() {
                if !out.contains(&local) {
                    out.push(local);
                }
            }
        }
    }
    out
}

/// A trait and every trait above it.
fn supertraits(tcx: TyCtxt<'_>, trait_def: DefId) -> Vec<DefId> {
    let mut out = vec![trait_def];
    let mut next = 0;
    while let Some(at) = out.get(next).copied() {
        next += 1;
        for (clause, _) in tcx.explicit_super_clauses_of(at).skip_binder() {
            if let Some(pred) = clause.as_trait_clause() {
                if !out.contains(&pred.def_id()) {
                    out.push(pred.def_id());
                }
            }
        }
    }
    out
}

/// A type with its references and boxes taken off.
fn unboxed(mut ty: Ty<'_>) -> Ty<'_> {
    loop {
        if let ty::Ref(_, inner, _) = ty.kind() {
            ty = *inner;
        } else if let Some(inner) = ty.boxed_ty() {
            ty = inner;
        } else {
            return ty;
        }
    }
}

/// Whether a value of this type may be a function value no type names: a type
/// parameter (`F: Fn(Ty) -> bool`), a trait object (`dyn Fn`), an `impl Fn`.
fn hides_a_function(ty: Ty<'_>) -> bool {
    if let ty::Param(_) | ty::Dynamic(..) | ty::Alias(..) = ty.kind() {
        return true;
    }
    false
}

/// A function of this crate with a body (a `fn`, a method, a trait's default
/// method), which the flow follows into and out of.
// A THIR argument may contain an opaque alias rigid in its analysis context.
// Instance selection uses the post-analysis context, so normalize the complete
// argument list there before asking codegen to resolve the callee. Passing the
// earlier rigid alias violates rustc's fully-normalized input requirement.
fn resolved_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    callee: DefId,
    args: <TyCtxt<'tcx> as ty::Interner>::GenericArgs,
) -> Option<ty::Instance<'tcx>> {
    let args = tcx
        .try_normalize_erasing_regions(typing_env, ty::set_aliases_to_non_rigid(tcx, args))
        .ok()?;
    ty::Instance::try_resolve(tcx, typing_env, callee, args)
        .ok()
        .flatten()
}

fn body_fn(tcx: TyCtxt<'_>, def: DefId) -> Option<LocalDefId> {
    let local = def.as_local()?;
    let (DefKind::Fn | DefKind::AssocFn) = tcx.def_kind(def) else {
        return None;
    };
    tcx.hir_maybe_body_owned_by(local)?;
    Some(local)
}

/// Which functions of this crate a call may run.
enum Target {
    /// The one the compiler resolved it to.
    One(LocalDefId),
    /// A method of a trait it could not resolve (a generic receiver, `dyn`):
    /// every body of this crate that implements it. The call's value carries
    /// all of its arguments, as another crate's does, and every variant any
    /// of them names in its result.
    Many(Vec<LocalDefId>),
    /// A function of another crate, a closure, an intrinsic.
    Outside,
}

/// Whether an expression reads a variable (see [`Flow::fixed`]).
struct Reads<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    reads: bool,
}

impl<'a, 'tcx> Visitor<'a, 'tcx> for Reads<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a Expr<'tcx>) {
        if let ExprKind::VarRef { .. }
        | ExprKind::UpvarRef { .. }
        | ExprKind::Closure(_)
        | ExprKind::InlineAsm(_)
        | ExprKind::Yield { .. } = expr.kind
        {
            self.reads = true;
            return;
        }
        visit::walk_expr(self, expr);
    }
}

/// The flow of named variants through one body.
struct Flow<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    thir: &'a Thir<'tcx>,
    holds: Holds<'tcx>,
    memo: Vec<Option<Src>>,
    breaks: Option<Src>,
    edges: Edges,
    refused: Vec<Refusal>,
}

impl<'a, 'tcx> Flow<'a, 'tcx> {
    /// What the value of `id` is computed from; nothing, for a value whose type
    /// cannot hold a gated enum.
    fn src(&mut self, id: ExprId) -> Src {
        if let Some(Some(known)) = self.memo.get(id.as_usize()) {
            return known.clone();
        }
        let thir = self.thir;
        let expr = &thir[id];
        let held = self.holds.held(expr.ty);
        let mut found = if held.carries() {
            self.value(id, expr)
        } else {
            Src::default()
        };
        // A value of a gated enum that reads no variable is one fixed variant,
        // whatever makes it: `Ty::default()`, `unit()`, `Ty::from(0)`,
        // `Key::default().kind`.
        if let ty::Adt(adt, _) = expr.ty.peel_refs().kind() {
            let key = enum_key(adt.did());
            if gated(self.tcx, *adt) && !found.named.contains_key(&key) && self.fixed(id) {
                let fixed = Src::named(
                    [key],
                    expr.span,
                    "a fixed variant (a value that reads no variable)",
                );
                found.join(&fixed);
            }
        }
        // A call of a gated crate's function that reads no variable is one
        // fixed value that this crate cannot follow into: it names what its
        // type holds, as a constant does (verifier land-clean-r1:
        // `CallingConv::all().contains(&c)`, `s == Sig::default()` and
        // `CallingConv::iter().any(..)` passed where `c == CallingConv::first()`
        // was refused).
        if held.carries() && self.calls_gated_crate(expr) && self.fixed(id) {
            let what = "a fixed value of a gated crate (a call of it that reads no variable)";
            found.join(&Src::fixed(&held, expr.span, what));
        }
        if !found.is_empty() {
            found.mask = held.mask();
        }
        for (enum_def, witness) in &found.named {
            self.edges
                .named
                .entry(*enum_def)
                .or_insert_with(|| witness.clone());
        }
        if let Some(slot) = self.memo.get_mut(id.as_usize()) {
            *slot = Some(found.clone());
        }
        found
    }

    fn union(&mut self, ids: impl IntoIterator<Item = ExprId>) -> Src {
        let mut out = Src::default();
        for id in ids {
            let one = self.src(id);
            out.join(&one);
        }
        out
    }

    /// Every value a `break` carries out of a loop or a labelled block.
    fn breaks(&mut self) -> Src {
        if let Some(known) = &self.breaks {
            return known.clone();
        }
        let thir = self.thir;
        let values: Vec<ExprId> = thir
            .exprs
            .iter()
            .filter_map(|expr| {
                if let ExprKind::Break { value, .. } = expr.kind {
                    return value;
                }
                None
            })
            .collect();
        let found = self.union(values);
        self.breaks = Some(found.clone());
        found
    }

    /// Which functions of this crate a call of `callee` runs: the one body
    /// the compiler resolves it to; for a trait method it cannot resolve (a
    /// generic receiver, `dyn`), every body of this crate implementing it.
    fn target(&self, callee: DefId, args: <TyCtxt<'tcx> as ty::Interner>::GenericArgs) -> Target {
        let tcx = self.tcx;
        let typing_env = ty::TypingEnv::post_analysis(tcx, self.def);
        if let Some(instance) = resolved_instance(tcx, typing_env, callee, args) {
            if let ty::InstanceKind::Item(def) = instance.def {
                return body_fn(tcx, def).map_or(Target::Outside, Target::One);
            }
        }
        let Some(trait_def) = tcx.trait_of_assoc(callee) else {
            return body_fn(tcx, callee).map_or(Target::Outside, Target::One);
        };
        let mut all: Vec<LocalDefId> = body_fn(tcx, callee).into_iter().collect();
        for imp in tcx.local_trait_impls(trait_def) {
            let item = tcx.impl_item_implementor_ids(imp.to_def_id()).get(&callee);
            all.extend(item.and_then(|item| body_fn(tcx, *item)));
        }
        Target::Many(all)
    }

    #[allow(clippy::too_many_lines)]
    fn value(&mut self, id: ExprId, expr: &Expr<'tcx>) -> Src {
        let tcx = self.tcx;
        let thir = self.thir;
        match &expr.kind {
            ExprKind::Scope { value: inner, .. }
            | ExprKind::ByUse { expr: inner, .. }
            | ExprKind::Deref { arg: inner }
            | ExprKind::Unary { arg: inner, .. }
            | ExprKind::Cast { source: inner }
            | ExprKind::ValueExpr { source: inner }
            | ExprKind::NeverToAny { source: inner }
            | ExprKind::PointerCoercion { source: inner, .. }
            | ExprKind::Field { lhs: inner, .. }
            | ExprKind::Index { lhs: inner, .. }
            | ExprKind::Borrow { arg: inner, .. }
            | ExprKind::RawBorrow { arg: inner, .. }
            | ExprKind::Repeat { value: inner, .. }
            | ExprKind::PlaceTypeAscription { source: inner, .. }
            | ExprKind::ValueTypeAscription { source: inner, .. }
            | ExprKind::PlaceUnwrapUnsafeBinder { source: inner }
            | ExprKind::ValueUnwrapUnsafeBinder { source: inner }
            | ExprKind::WrapUnsafeBinder { source: inner }
            | ExprKind::Reborrow { source: inner, .. } => self.src(*inner),
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::LogicalOp { lhs, rhs, .. } => {
                self.union([*lhs, *rhs])
            }
            ExprKind::Array { fields } | ExprKind::Tuple { fields } => {
                self.union(fields.iter().copied())
            }
            ExprKind::Adt(adt) => {
                if gated(tcx, adt.adt_def) {
                    let path = tcx.def_path_str(adt.adt_def.variant(adt.variant_index).def_id);
                    let key = enum_key(adt.adt_def.did());
                    return Src::named([key], expr.span, &format!("`{path}`"));
                }
                let base = if let AdtExprBase::Base(fru) = &adt.base {
                    Some(fru.base)
                } else {
                    None
                };
                self.union(adt.fields.iter().map(|field| field.expr).chain(base))
            }
            // A constant stands for every gated variant its type can hold.
            ExprKind::NamedConst { def_id, .. } | ExprKind::ConstParam { def_id, .. } => {
                let what = format!("the constant `{}`", tcx.def_path_str(*def_id));
                Src::fixed(&self.holds.held(expr.ty), expr.span, &what)
            }
            ExprKind::ConstBlock { .. } => {
                Src::fixed(&self.holds.held(expr.ty), expr.span, "an inline constant")
            }
            ExprKind::StaticRef { def_id, .. } | ExprKind::ThreadLocalRef(def_id) => {
                let what = format!("the static `{}`", tcx.def_path_str(*def_id));
                Src::fixed(&self.holds.held(expr.ty), expr.span, &what)
            }
            ExprKind::ZstLiteral { .. } => {
                let ty::FnDef(def, _) = expr.ty.kind() else {
                    return Src::default();
                };
                // A variant's constructor, passed as a function.
                if let DefKind::Ctor(CtorOf::Variant, _) = tcx.def_kind(*def) {
                    let variant = tcx.parent(*def);
                    let enum_def = tcx.parent(variant);
                    if gated(tcx, tcx.adt_def(enum_def)) {
                        let path = tcx.def_path_str(variant);
                        let key = enum_key(enum_def);
                        return Src::named([key], expr.span, &format!("`{path}`"));
                    }
                }
                // A function of this crate, passed as one: what it names in its
                // result.
                let mut out = Src::default();
                if let Some(local) = body_fn(tcx, *def) {
                    out.fn_items.insert(def_key(local));
                }
                out
            }
            ExprKind::VarRef { id } => {
                let mut out = Src::default();
                out.vars.insert(var_key(id.0));
                out
            }
            ExprKind::UpvarRef { var_hir_id, .. } => {
                let mut out = Src::default();
                out.vars.insert(var_key(var_hir_id.0));
                out
            }
            ExprKind::Call { ty, fun, args, .. } => {
                // A function of this crate is followed through its body: its
                // result is resolved per call. Any other callee (std's
                // containers, iterators and conversions; a closure; a function
                // pointer; a trait method no single body of this crate
                // implements) may hand back anything it was given.
                let at = (def_key(self.def), index_key(id.as_usize()));
                if let ty::FnDef(callee, fn_args) = ty.kind() {
                    match self.target(*callee, tcx.instantiate_bound_regions_with_erased(*fn_args))
                    {
                        Target::One(_) => {
                            let mut out = Src::default();
                            out.calls.insert(at);
                            return out;
                        }
                        // What any of the bodies always returns, or names
                        // for a call that reads no variable, beside all it
                        // was given.
                        Target::Many(_) => {
                            let mut out =
                                self.union(std::iter::once(*fun).chain(args.iter().copied()));
                            out.calls.insert(at);
                            return out;
                        }
                        // What this crate's trait impls it may run name in
                        // their results, beside all it was given.
                        Target::Outside => {
                            let mut out =
                                self.union(std::iter::once(*fun).chain(args.iter().copied()));
                            if !self
                                .reentries(
                                    *callee,
                                    tcx.instantiate_bound_regions_with_erased(*fn_args),
                                )
                                .is_empty()
                            {
                                out.calls.insert(at);
                            }
                            return out;
                        }
                    }
                }
                self.union(std::iter::once(*fun).chain(args.iter().copied()))
            }
            ExprKind::If { then, else_opt, .. } => {
                self.union(std::iter::once(*then).chain(*else_opt))
            }
            ExprKind::Match { arms, .. } => self.union(arms.iter().map(|arm| thir[*arm].body)),
            ExprKind::LoopMatch { match_data, .. } => {
                self.union(match_data.arms.iter().map(|arm| thir[*arm].body))
            }
            ExprKind::Block { block } => {
                let block = &thir[*block];
                let mut out = self.union(block.expr);
                if block.targeted_by_break {
                    let broken = self.breaks();
                    out.join(&broken);
                }
                out
            }
            ExprKind::Loop { .. } => self.breaks(),
            ExprKind::Closure(closure) => {
                let mut out = self.union(closure.upvars.iter().copied());
                out.closure_results.insert(def_key(closure.closure_id));
                out
            }
            // No value (`!`, `()`, a `bool` condition), or one written by no
            // pattern or constructor: a literal, inline assembly, a resumed
            // coroutine's argument.
            ExprKind::Let { .. }
            | ExprKind::Assign { .. }
            | ExprKind::AssignOp { .. }
            | ExprKind::Break { .. }
            | ExprKind::Continue { .. }
            | ExprKind::ConstContinue { .. }
            | ExprKind::Return { .. }
            | ExprKind::Become { .. }
            | ExprKind::Literal { .. }
            | ExprKind::NonHirLiteral { .. }
            | ExprKind::InlineAsm(_)
            | ExprKind::Yield { .. } => Src::default(),
        }
    }

    /// Whether `expr` is a call of a function of [`ENUM_CRATES`] -- by its
    /// path, or by the impl a trait method resolves to (`Sig::default()` is
    /// core's `Default::default`, resolved to the gated crate's impl).
    fn calls_gated_crate(&self, expr: &Expr<'tcx>) -> bool {
        let tcx = self.tcx;
        let ExprKind::Call { ty: fn_ty, .. } = &expr.kind else {
            return false;
        };
        let ty::FnDef(callee, fn_args) = fn_ty.kind() else {
            return false;
        };
        let gated_crate = |did: DefId| ENUM_CRATES.contains(&tcx.crate_name(did.krate).as_str());
        if gated_crate(*callee) {
            return true;
        }
        let typing_env = ty::TypingEnv::post_analysis(tcx, self.def);
        resolved_instance(
            tcx,
            typing_env,
            *callee,
            tcx.instantiate_bound_regions_with_erased(*fn_args),
        )
        .is_some_and(|instance| gated_crate(instance.def_id()))
    }

    /// Whether the value of `id` reads no variable (and no closure, which
    /// captures some): literals, constants and variants, and what calls and
    /// operators make of them.
    fn fixed(&self, id: ExprId) -> bool {
        let mut reads = Reads {
            thir: self.thir,
            reads: false,
        };
        reads.visit_expr(&self.thir[id]);
        !reads.reads
    }

    /// The variable a place expression is rooted at.
    fn root_var(&self, id: ExprId) -> Option<Var> {
        let thir = self.thir;
        match &thir[id].kind {
            ExprKind::VarRef { id } => Some(var_key(id.0)),
            ExprKind::UpvarRef { var_hir_id, .. } => Some(var_key(var_hir_id.0)),
            ExprKind::Scope { value: inner, .. }
            | ExprKind::Deref { arg: inner }
            | ExprKind::Borrow { arg: inner, .. }
            | ExprKind::RawBorrow { arg: inner, .. }
            | ExprKind::Field { lhs: inner, .. }
            | ExprKind::Index { lhs: inner, .. }
            | ExprKind::PlaceTypeAscription { source: inner, .. }
            | ExprKind::PlaceUnwrapUnsafeBinder { source: inner }
            | ExprKind::PointerCoercion { source: inner, .. }
            | ExprKind::ValueExpr { source: inner }
            | ExprKind::Reborrow { source: inner, .. } => self.root_var(*inner),
            // An overloaded place (`*v`, `v[i]` through `Deref` / `Index`), or
            // what a call hands back into its receiver (`*v.last_mut().unwrap()`,
            // `*cell.borrow_mut()`): the place its first argument is.
            ExprKind::Call { args, .. } => args.first().and_then(|first| self.root_var(*first)),
            ExprKind::If { .. }
            | ExprKind::ByUse { .. }
            | ExprKind::Binary { .. }
            | ExprKind::LogicalOp { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Cast { .. }
            | ExprKind::NeverToAny { .. }
            | ExprKind::Loop { .. }
            | ExprKind::LoopMatch { .. }
            | ExprKind::Let { .. }
            | ExprKind::Match { .. }
            | ExprKind::Block { .. }
            | ExprKind::Assign { .. }
            | ExprKind::AssignOp { .. }
            | ExprKind::Break { .. }
            | ExprKind::Continue { .. }
            | ExprKind::ConstContinue { .. }
            | ExprKind::Return { .. }
            | ExprKind::Become { .. }
            | ExprKind::ConstBlock { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::Array { .. }
            | ExprKind::Tuple { .. }
            | ExprKind::Adt(_)
            | ExprKind::ValueTypeAscription { .. }
            | ExprKind::ValueUnwrapUnsafeBinder { .. }
            | ExprKind::WrapUnsafeBinder { .. }
            | ExprKind::Closure(_)
            | ExprKind::Literal { .. }
            | ExprKind::NonHirLiteral { .. }
            | ExprKind::ZstLiteral { .. }
            | ExprKind::NamedConst { .. }
            | ExprKind::ConstParam { .. }
            | ExprKind::StaticRef { .. }
            | ExprKind::InlineAsm(_)
            | ExprKind::ThreadLocalRef(_)
            | ExprKind::Yield { .. } => None,
        }
    }

    /// Every variable `pat` binds takes what the value it matches is computed
    /// from.
    ///
    /// A binding that can write into what it was bound from -- a `&mut`, a
    /// `&Cell`, an `Rc<RefCell<..>>`, an iterator of `&mut`, anything holding
    /// one -- is an alias of those variables: what is written through it is
    /// written into them (`let r = &mut v; r.push(Ty::A)`).
    fn bind(&mut self, pat: &Pat<'tcx>, src: &Src) {
        if src.is_empty() {
            return;
        }
        if let PatKind::Binding { var, ty, .. } = &pat.kind {
            let key = var_key(var.0);
            self.edges.vars.push((key, src.clone()));
            if self.aliases(*ty) {
                let mut through = Src::default();
                through.vars.insert(key);
                for from in &src.vars {
                    self.edges.vars.push((*from, through.clone()));
                }
            }
        }
        visit_subpatterns(pat, &mut |sub| self.bind(sub, src));
    }

    /// Whether a value of this type can write into what it was made from: it
    /// holds a `&mut` or is not `Freeze` (a `Cell`, a `RefCell`, an `Rc`), and
    /// it can carry a gated enum.
    fn aliases(&mut self, ty: Ty<'tcx>) -> bool {
        let tcx = self.tcx;
        self.holds.carries(ty)
            && (self.mutable_inside(ty)
                || !ty.is_freeze(tcx, ty::TypingEnv::post_analysis(tcx, self.def)))
    }

    /// Whether a type holds a `&mut`, a `*mut` or a reference to a type that
    /// is not `Freeze` anywhere, its fields included (`slice::IterMut` holds a
    /// `PhantomData<&mut T>`; `&Cell<T>` writes through `set`), walked with a
    /// work list up to [`HELD_LIMIT`] types (recursion overflowed the stack on
    /// a compiler's own types).
    fn mutable_inside(&self, root: Ty<'tcx>) -> bool {
        let tcx = self.tcx;
        let typing_env = ty::TypingEnv::post_analysis(tcx, self.def);
        let mut seen: HashSet<Ty<'tcx>> = HashSet::new();
        let mut todo = vec![root];
        while let Some(ty) = todo.pop() {
            if !seen.insert(ty) {
                continue;
            }
            // Past the limit, it may hold one.
            if seen.len() > HELD_LIMIT {
                return true;
            }
            match ty.kind() {
                ty::Ref(_, inner, mutability) | ty::RawPtr(inner, mutability) => {
                    if mutability.is_mut() || !inner.is_freeze(tcx, typing_env) {
                        return true;
                    }
                    todo.push(*inner);
                }
                &ty::Adt(adt, args) => {
                    todo.extend(args.types());
                    for field in adt.all_fields() {
                        todo.push(field.ty(tcx, args).skip_normalization());
                    }
                }
                ty::Tuple(elems) => todo.extend(elems.iter()),
                ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => todo.push(*inner),
                ty::Closure(_, args) => todo.extend(args.as_closure().upvar_tys()),
                // A function holds no data; what its signature names is under
                // its binder.
                ty::FnDef(..) | ty::FnPtr(..) => {}
                // What a trait object's or a projection's bounds, or a
                // coroutine's arguments, write in it.
                ty::Dynamic(..)
                | ty::Alias(..)
                | ty::Coroutine(..)
                | ty::CoroutineClosure(..)
                | ty::CoroutineWitness(..)
                | ty::UnsafeBinder(_) => todo.extend(
                    ty.walk()
                        .skip(1)
                        .filter_map(|arg| arg.as_type())
                        .filter(|inner| !inner.has_escaping_bound_vars()),
                ),
                ty::Bool
                | ty::Char
                | ty::Int(_)
                | ty::Uint(_)
                | ty::Float(_)
                | ty::Str
                | ty::Never
                | ty::Foreign(_)
                | ty::Param(_)
                | ty::Bound(..)
                | ty::Placeholder(_)
                | ty::Infer(_)
                | ty::Error(_) => {}
            }
        }
        false
    }

    /// Every variable `pat` binds, with its type.
    fn bound_typed(pat: &Pat<'tcx>, out: &mut Vec<(Var, Ty<'tcx>)>) {
        if let PatKind::Binding { var, ty, .. } = &pat.kind {
            out.push((var_key(var.0), *ty));
        }
        visit_subpatterns(pat, &mut |sub| Self::bound_typed(sub, out));
    }

    /// Every variable `pat` binds.
    fn bound(pat: &Pat<'tcx>, out: &mut Vec<Var>) {
        if let PatKind::Binding { var, .. } = &pat.kind {
            out.push(var_key(var.0));
        }
        visit_subpatterns(pat, &mut |sub| Self::bound(sub, out));
    }

    /// Whether a value of type `ty` is a reference the callee can write
    /// through (`&mut`, or `&` to a type that is not `Freeze`: `Cell::set`,
    /// `RefCell::replace`) to something that can hold a gated enum.
    fn writable(&mut self, ty: Ty<'tcx>) -> bool {
        let ty::Ref(_, inner, mutability) = ty.kind() else {
            return false;
        };
        let writes = mutability.is_mut()
            || !inner.is_freeze(self.tcx, ty::TypingEnv::post_analysis(self.tcx, self.def));
        writes && self.holds.carries(*inner)
    }

    /// The trait bounds a call of `callee` holds, each as the trait, the types
    /// it bounds (normalized where a concrete type resolves them), and whether
    /// it is a where-clause: the function's own and its impl's, and those of
    /// the impl method the call resolves to and of that impl -- and, not a
    /// where-clause, the trait a method belongs to (a trait's own supertraits
    /// are not the call's: a trait with an `Eq` supertrait does not compare in
    /// each method).
    fn bounds(
        &self,
        callee: DefId,
        args: <TyCtxt<'tcx> as ty::Interner>::GenericArgs,
    ) -> Vec<Bound<'tcx>> {
        let tcx = self.tcx;
        let mut out = Vec::new();
        if let Some(trait_def) = tcx.trait_of_assoc(callee) {
            let tys = args.types().map(|ty| self.normalized(ty)).collect();
            out.push((trait_def, tys, false));
        }
        let mut bounded = vec![(callee, args)];
        let typing_env = ty::TypingEnv::post_analysis(tcx, self.def);
        if let Some(instance) = resolved_instance(tcx, typing_env, callee, args) {
            if let ty::InstanceKind::Item(def) = instance.def {
                if def != callee {
                    bounded.push((def, instance.args));
                }
            }
        }
        for (def, args) in bounded {
            for item in std::iter::once(def).chain(tcx.impl_of_assoc(def)) {
                for (clause, _) in tcx.clauses_of(item).instantiate_own(tcx, args) {
                    if let Some(pred) = clause.skip_normalization().as_trait_clause() {
                        let pred = tcx.instantiate_bound_regions_with_erased(pred);
                        let tys = pred
                            .trait_ref
                            .args
                            .types()
                            .map(|ty| self.normalized(ty))
                            .collect();
                        out.push((pred.def_id(), tys, true));
                    }
                }
            }
        }
        out
    }

    /// A type with its projections normalized where a concrete type resolves
    /// them (`<Map<Iter<'_, F>, {closure}> as Iterator>::Item` is what the
    /// closure returns), `impl Trait`s left as they are.
    fn normalized(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        let tcx = self.tcx;
        let typing_env = ty::TypingEnv::non_body_analysis(tcx, self.def);
        tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(ty))
            .unwrap_or(ty)
    }

    /// The gated enums comparing values of `tys` tells apart: `None`, any (a
    /// type that may hold any).
    fn compared(&mut self, tys: impl IntoIterator<Item = Ty<'tcx>>) -> Option<BTreeSet<Enum>> {
        let mut out = BTreeSet::new();
        for ty in tys {
            let held = self.holds.held(ty);
            if held.hidden {
                return None;
            }
            out.extend(held.enums);
        }
        Some(out)
    }

    /// The comparison a call makes: a method of a comparison trait (an
    /// operand that names a variant has a type that can hold one), or a
    /// function whose bounds compare a type that can hold a gated enum --
    /// its own (`contains`, `strip_prefix`, a map's `get`), its impl's
    /// (`HashSet::insert`, `HashMap::entry`, `HashSet::difference`,
    /// `Vec::dedup`), or those of the impl a trait method resolves to
    /// (`map[&k]`, `Index` of a `HashMap`). For a callee whose body the flow
    /// does not follow (`followed` false), a bound whose trait has a
    /// comparison supertrait compares too: nothing else shows what it does
    /// with the bound.
    ///
    /// Returns what it is and the gated enums it compares (`None`, any).
    fn comparison(
        &mut self,
        callee: DefId,
        args: <TyCtxt<'tcx> as ty::Interner>::GenericArgs,
        followed: bool,
    ) -> Option<(String, Option<BTreeSet<Enum>>)> {
        let tcx = self.tcx;
        if tcx
            .opt_parent(callee)
            .is_some_and(|parent| comparison_trait(tcx, parent))
        {
            let tys: Vec<Ty<'tcx>> = args.types().map(|ty| self.normalized(ty)).collect();
            let enums = self.compared(tys);
            return Some((format!("`{}`", tcx.def_path_str(callee)), enums));
        }
        for (bound, tys, clause) in self.bounds(callee, args) {
            let compares = comparison_trait(tcx, bound)
                || clause
                    && !followed
                    && supertraits(tcx, bound)
                        .into_iter()
                        .any(|above| comparison_trait(tcx, above));
            if !compares {
                continue;
            }
            let enums = self.compared(tys);
            if enums.as_ref().is_none_or(|enums| !enums.is_empty()) {
                let what = format!(
                    "`{}` (its `{}` bound)",
                    tcx.def_path_str(callee),
                    tcx.def_path_str(bound)
                );
                return Some((what, enums));
            }
        }
        None
    }

    /// The edges and comparisons of the whole body.
    fn run(&mut self, def: LocalDefId, root: ExprId) {
        let tcx = self.tcx;
        let thir = self.thir;
        let closure = tcx.is_closure_like(def.to_def_id());
        let function = body_fn(tcx, def.to_def_id()).is_some();
        let mut returned = vec![root];
        // A function of this crate coerced to a function pointer (`let p:
        // fn(Ty) = same`, `g(same)` for `g(p: fn(Ty))`) is taken as a value: a
        // call through a pointer with as many parameters may run it. Passed
        // as itself (`any(eq_pair)`), it is the argument the callee calls, and
        // called by its name, the callee (verifier land-clean-r1 NOTE: every
        // function named anywhere but as a callee, and so every one called by
        // its path under the scope that wraps it, counted as taken as a value,
        // and every call through a pointer with as many arguments anywhere in
        // the crate fed its parameters).
        //
        // What each call is passed, under its scopes and borrows -- not under
        // a coercion to a pointer, which a call through a pointer runs.
        let mut passed = BTreeSet::new();
        let mut callees = BTreeSet::new();
        for expr in &thir.exprs {
            if let ExprKind::Call { fun, args, .. } = &expr.kind {
                passed.extend(args.iter().map(|arg| self.core(*arg).as_usize()));
                callees.insert(self.core(*fun).as_usize());
            }
        }
        for (index, expr) in thir.exprs.iter().enumerate() {
            if let ExprKind::PointerCoercion { source, .. } = expr.kind {
                let erased = closures_of(thir[source].ty);
                self.edges.erased.extend(erased.into_iter().map(def_key));
                if let ty::FnDef(item, item_args) = thir[source].ty.kind() {
                    let bodies = match self
                        .target(*item, tcx.instantiate_bound_regions_with_erased(*item_args))
                    {
                        Target::One(one) => vec![one],
                        Target::Many(all) => all,
                        Target::Outside => Vec::new(),
                    };
                    for body in bodies {
                        let arity = tcx.fn_sig(body).skip_binder().skip_binder().inputs().len();
                        self.edges.reified.push((def_key(body), arity));
                    }
                }
            }
            // A comparison taken as a value that no call is passed as itself
            // (kept in a variable, a field, a result; coerced to a pointer):
            // what it compares is not followed.
            let (ExprKind::ZstLiteral { .. }, ty::FnDef(item, item_args)) =
                (&expr.kind, expr.ty.kind())
            else {
                continue;
            };
            if callees.contains(&index)
                || passed.contains(&index)
                || body_fn(tcx, *item).is_some()
                || from_assertion(tcx, expr.span)
                || from_builtin_derive(tcx, expr.span)
            {
                continue;
            }
            let what = match self.comparison(
                *item,
                tcx.instantiate_bound_regions_with_erased(*item_args),
                false,
            ) {
                Some((what, None)) => what,
                Some((what, Some(enums))) if !enums.is_empty() => what,
                Some((_, Some(_))) | None => continue,
            };
            self.refused.push(Refusal {
                span: expr.span,
                why: format!("{what}, a comparison taken as a value that no call is passed as itself: what it compares is not followed -- refused, not judged (it may be {CATCH_ALL})"),
                told: None,
            });
        }
        for (index, expr) in thir.exprs.iter().enumerate() {
            let id = ExprId::from_usize(index);
            match &expr.kind {
                ExprKind::Let {
                    expr: scrutinee,
                    pat,
                } => {
                    let src = self.src(*scrutinee);
                    self.bind(pat, &src);
                }
                ExprKind::Match {
                    scrutinee, arms, ..
                } => {
                    let src = self.src(*scrutinee);
                    for arm in arms.iter() {
                        self.bind(&thir[*arm].pattern, &src);
                    }
                }
                ExprKind::LoopMatch { match_data, .. } => {
                    let src = self.src(match_data.scrutinee);
                    for arm in match_data.arms.iter() {
                        self.bind(&thir[*arm].pattern, &src);
                    }
                }
                ExprKind::Assign { lhs, rhs } => {
                    if let Some(var) = self.root_var(*lhs) {
                        let src = self.src(*rhs);
                        if !src.is_empty() {
                            self.edges.vars.push((var, src));
                        }
                    }
                }
                ExprKind::Return { value: Some(value) } => returned.push(*value),
                ExprKind::Call { ty, args, .. } => self.call(id, *ty, args),
                // Every expression of the source is wrapped in a scope that
                // names it: a cast is read off the source and its type-check,
                // since the THIR of `Enum::Variant as u8` is already the number.
                ExprKind::Scope { hir_id, .. } => self.cast(def, *hir_id),
                ExprKind::Cast { .. }
                | ExprKind::If { .. }
                | ExprKind::ByUse { .. }
                | ExprKind::Deref { .. }
                | ExprKind::Binary { .. }
                | ExprKind::LogicalOp { .. }
                | ExprKind::Unary { .. }
                | ExprKind::ValueExpr { .. }
                | ExprKind::NeverToAny { .. }
                | ExprKind::PointerCoercion { .. }
                | ExprKind::Loop { .. }
                | ExprKind::Block { .. }
                | ExprKind::AssignOp { .. }
                | ExprKind::Field { .. }
                | ExprKind::Index { .. }
                | ExprKind::VarRef { .. }
                | ExprKind::UpvarRef { .. }
                | ExprKind::Borrow { .. }
                | ExprKind::RawBorrow { .. }
                | ExprKind::Break { .. }
                | ExprKind::Continue { .. }
                | ExprKind::ConstContinue { .. }
                | ExprKind::Return { value: None }
                | ExprKind::Become { .. }
                | ExprKind::ConstBlock { .. }
                | ExprKind::Repeat { .. }
                | ExprKind::Array { .. }
                | ExprKind::Tuple { .. }
                | ExprKind::Adt(_)
                | ExprKind::PlaceTypeAscription { .. }
                | ExprKind::ValueTypeAscription { .. }
                | ExprKind::PlaceUnwrapUnsafeBinder { .. }
                | ExprKind::ValueUnwrapUnsafeBinder { .. }
                | ExprKind::WrapUnsafeBinder { .. }
                | ExprKind::Closure(_)
                | ExprKind::Literal { .. }
                | ExprKind::NonHirLiteral { .. }
                | ExprKind::ZstLiteral { .. }
                | ExprKind::NamedConst { .. }
                | ExprKind::ConstParam { .. }
                | ExprKind::StaticRef { .. }
                | ExprKind::InlineAsm(_)
                | ExprKind::ThreadLocalRef(_)
                | ExprKind::Yield { .. }
                | ExprKind::Reborrow { .. } => {}
            }
        }
        for stmt in thir.stmts.iter() {
            if let StmtKind::Let {
                pattern,
                initializer: Some(init),
                ..
            } = &stmt.kind
            {
                let src = self.src(*init);
                self.bind(pattern, &src);
            }
        }
        let key = def_key(def);
        if closure {
            let mut param = Src::default();
            param.closure_params.insert(key);
            for pat in thir.params.iter().filter_map(|param| param.pat.as_deref()) {
                self.bind(pat, &param);
                // What it writes through a parameter (`|x| *x = Ty::A`) is
                // written into what the call it is passed to hands it.
                let mut bound = Vec::new();
                Self::bound_typed(pat, &mut bound);
                for (var, ty) in bound {
                    if self.aliases(ty) {
                        let mut through = Src::default();
                        through.vars.insert(var);
                        self.edges.closure_writes.push((key, through));
                    }
                }
            }
            for value in returned {
                let src = self.src(value);
                self.edges.closure_results.push((key, src));
            }
        } else if function {
            self.function(key, &returned);
        }
    }

    /// A function of this crate: its parameters are what its calls pass; its
    /// result and what it writes through a parameter are resolved per call.
    fn function(&mut self, key: u32, returned: &[ExprId]) {
        let thir = self.thir;
        let outside = self.called_from_outside();
        for (index, param) in thir.params.iter().enumerate() {
            let Some(pat) = param.pat.as_deref() else {
                continue;
            };
            let position = (key, index_key(index));
            if self.holds.carries(param.ty) {
                let mut src = Src::default();
                src.params.insert(position);
                src.mask = self.holds.mask(param.ty);
                self.bind(pat, &src);
                // Called where no call of this crate shows what it passes.
                if let Some(path) = &outside {
                    let what = format!(
                        "any variant the crate names (a parameter of `{path}`, which another crate or the compiler calls with any value)"
                    );
                    let any = Src {
                        every: Some((pat.span, what)),
                        mask: self.holds.mask(param.ty),
                        ..Src::default()
                    };
                    self.edges.params.push((position, any));
                }
            }
            if self.writable(param.ty) {
                let mut vars = Vec::new();
                Self::bound(pat, &mut vars);
                for var in vars {
                    let mut through = Src::default();
                    through.vars.insert(var);
                    through.mask = self.holds.mask(param.ty);
                    self.edges.writes.push((position, through));
                }
            }
        }
        for value in returned {
            let src = self.src(*value);
            self.edges.results.push((key, src));
        }
    }

    /// The path of this body when it is a method of this crate's impl of
    /// another crate's trait (`Display::fmt`, `Iterator::next`, `Drop::drop`,
    /// `From::from`): that crate calls it, or the compiler does, and no call of
    /// this crate shows with what. A comparison trait's impl is left out: each
    /// call of it is a comparison, judged where it is made.
    fn called_from_outside(&self) -> Option<String> {
        let tcx = self.tcx;
        let def = self.def.to_def_id();
        let imp = tcx.trait_impl_of_assoc(def)?;
        let trait_def = tcx.impl_trait_id(imp);
        if trait_def.is_local() || comparison_trait(tcx, trait_def) {
            return None;
        }
        Some(tcx.def_path_str(def))
    }

    /// The methods of this crate's impls of other crates' traits that a call
    /// of another crate's function may run: for each bound the call holds on a
    /// type of this crate (`T: Default` of `opt.unwrap_or_default()`, `Self:
    /// Iterator` of `w.take(3)`, `I: Iterator` of `Take<W>`'s `next`), the
    /// methods of every impl of that trait, or of a supertrait of it, whose
    /// header names that type -- of every impl, for a bound on a type that may
    /// be any (a type parameter, a trait object, an `impl Trait` hiding a type
    /// of this crate: `fn w() -> impl Iterator<Item = Ty> { W { .. } }`). Only
    /// a method whose result can carry a variant is one: a call of it hands
    /// nothing else back.
    fn reentries(
        &mut self,
        callee: DefId,
        fn_args: <TyCtxt<'tcx> as ty::Interner>::GenericArgs,
    ) -> Vec<LocalDefId> {
        let tcx = self.tcx;
        let local_adts = |ty: Ty<'tcx>| {
            ty.walk().filter_map(|arg| {
                if let Some(ty::Adt(adt, _)) = arg.as_type().map(|inner| inner.kind()) {
                    return adt.did().as_local().map(def_key);
                }
                None
            })
        };
        let any_type = |ty: Ty<'tcx>| {
            ty.walk().any(|arg| {
                arg.as_type().is_some_and(|inner| {
                    if let ty::Param(_) | ty::Dynamic(..) | ty::Alias(..) = inner.kind() {
                        return true;
                    }
                    false
                })
            })
        };
        let mut out = Vec::new();
        for (bound, tys, _) in self.bounds(callee, fn_args) {
            if bound.is_local() {
                continue;
            }
            let any = tys.iter().any(|ty| any_type(*ty));
            let local: BTreeSet<u32> = tys.into_iter().flat_map(local_adts).collect();
            if local.is_empty() && !any {
                continue;
            }
            for trait_def in supertraits(tcx, bound) {
                for imp in tcx.local_trait_impls(trait_def) {
                    let header = tcx.impl_trait_ref(imp.to_def_id()).skip_binder();
                    if !any
                        && !header
                            .args
                            .types()
                            .flat_map(local_adts)
                            .any(|adt| local.contains(&adt))
                    {
                        continue;
                    }
                    for item in tcx.associated_item_def_ids(imp.to_def_id()) {
                        let Some(body) = body_fn(tcx, *item) else {
                            continue;
                        };
                        let output = tcx.fn_sig(body).skip_binder().skip_binder().output();
                        if !out.contains(&body) && self.holds.carries(output) {
                            out.push(body);
                        }
                    }
                }
            }
        }
        out
    }

    /// A gated enum cast to a number: the number stands for every variant.
    fn cast(&mut self, def: LocalDefId, hir_id: HirId) {
        let tcx = self.tcx;
        let rustc_hir::Node::Expr(expr) = tcx.hir_node(hir_id) else {
            return;
        };
        let rustc_hir::ExprKind::Cast(source, _) = expr.kind else {
            return;
        };
        let from = tcx.typeck(def).expr_ty(source);
        if matches_adt_gated(tcx, from) {
            let to = tcx.typeck(def).expr_ty(expr);
            self.refused.push(Refusal {
                span: expr.span,
                why: format!(
                    "`{from}` cast to `{to}` -- a discriminant cast is {CATCH_ALL}: the number stands for every variant, present and future, and compiles unchanged when the enum gains one; name the variants in a `match`"
                ),
                told: None,
            });
        }
    }

    /// A call: a closure or a function of this crate it is passed feeds its
    /// parameters from the other arguments; a function of this crate it
    /// runs takes its arguments into its parameters and is resolved per call;
    /// any other callee's writable argument takes what the others carry, and
    /// a function value it is passed is called with them; and a comparison is
    /// a sink -- so is a comparison passed as a value.
    #[allow(clippy::too_many_lines)]
    fn call(&mut self, id: ExprId, fn_ty: Ty<'tcx>, args: &[ExprId]) {
        let tcx = self.tcx;
        let thir = self.thir;
        let at = (def_key(self.def), index_key(id.as_usize()));
        let srcs: Vec<Src> = args.iter().map(|arg| self.src(*arg)).collect();
        let others = |skip: usize| {
            let mut out = Src::default();
            for (index, src) in srcs.iter().enumerate() {
                if index != skip {
                    out.join(src);
                }
            }
            out
        };
        let target = if let ty::FnDef(callee, fn_args) = fn_ty.kind() {
            self.target(*callee, tcx.instantiate_bound_regions_with_erased(*fn_args))
        } else {
            Target::Outside
        };
        // The bodies of this crate the call runs, whose parameters it feeds;
        // whether another crate's code may run instead (or as well).
        let (bodies, outside) = match &target {
            Target::One(one) => (vec![*one], false),
            Target::Many(all) => (all.clone(), true),
            Target::Outside => (Vec::new(), true),
        };
        // A call through a function pointer runs any function of this crate
        // taken as a value with as many parameters.
        if let ty::FnPtr(..) = fn_ty.kind() {
            self.edges.pointer_calls.push((srcs.len(), srcs.clone()));
        }
        for (index, arg) in args.iter().enumerate() {
            // A function pointer passed on: the callee may call it with the
            // call's other arguments.
            if let ty::FnPtr(sig_tys, _) = thir[*arg].ty.peel_refs().kind() {
                let arity = sig_tys.skip_binder().inputs().len();
                self.edges
                    .pointer_calls
                    .push((arity, vec![others(index); arity]));
            }
            let arg_ty = thir[*arg].ty.peel_refs();
            for closure in self.closures_in(*arg) {
                self.edges
                    .closure_params
                    .push((def_key(closure), others(index)));
            }
            if let ty::FnDef(item, item_args) = arg_ty.kind() {
                let items = match self
                    .target(*item, tcx.instantiate_bound_regions_with_erased(*item_args))
                {
                    Target::One(one) => vec![one],
                    Target::Many(all) => all,
                    Target::Outside => Vec::new(),
                };
                for body in items {
                    let count = tcx.fn_sig(body).skip_binder().skip_binder().inputs().len();
                    for position in 0..count {
                        let key = (def_key(body), index_key(position));
                        self.edges.params.push((key, others(index)));
                    }
                }
            }
            // A function value that is a parameter of this function (or a
            // variable holding one) passed on (`[..].iter().any(f)` in `fn
            // apply<F: Fn(Ty) -> bool>(f: F)`): another crate's callee may call
            // it with the call's other arguments, and a function of this crate
            // calls it as its own parameter is called.
            let src = &srcs[index];
            if hides_a_function(unboxed(arg_ty)) && !(src.params.is_empty() && src.vars.is_empty())
            {
                if outside {
                    self.edges.callbacks.push((src.clone(), others(index)));
                }
                for body in &bodies {
                    let param = (def_key(*body), index_key(index));
                    self.edges.forwards.push((src.clone(), param));
                }
            }
            self.passed_comparison(*arg, index, &bodies, &others);
        }
        let mut writes = Vec::new();
        let mut closures = Vec::new();
        for (index, arg) in args.iter().enumerate() {
            if self.writable(thir[*arg].ty) {
                if let Some(var) = self.root_var(*arg) {
                    writes.push((index_key(index), var));
                }
            }
            for closure in self.closures_in(*arg) {
                closures.push((index_key(index), def_key(closure)));
            }
        }
        // A closure passed with other arguments may be handed references into
        // them (`v.iter_mut().for_each(|x| *x = Ty::A)`): what it writes
        // through its parameters is written into their variables.
        for (at, closure) in &closures {
            for (index, arg) in args.iter().enumerate() {
                if index_key(index) == *at {
                    continue;
                }
                if let Some(var) = self.root_var(*arg) {
                    let mut written = Src::default();
                    written.closure_writes.insert(*closure);
                    self.edges.vars.push((var, written));
                }
            }
        }
        // A closure or function value called (`f(x)` is `Fn::call(&f, (x,))`):
        // what it is called with feeds what `f` is -- a parameter of this
        // function, resolved at each call of it.
        if let ty::FnDef(callee, _) = fn_ty.kind() {
            let through_fn_trait = tcx
                .trait_of_assoc(*callee)
                .is_some_and(|parent| tcx.fn_trait_kind_from_def_id(parent).is_some());
            if let (true, [receiver, arguments]) = (through_fn_trait, srcs.as_slice()) {
                if !receiver.params.is_empty() || !receiver.vars.is_empty() {
                    self.edges
                        .callbacks
                        .push((receiver.clone(), arguments.clone()));
                }
                // A `dyn Fn` called: any closure of this crate erased to one
                // may run.
                if let Some(called) = args.first() {
                    if let ty::Dynamic(..) = unboxed(thir[*called].ty).kind() {
                        self.edges.erased_calls.push(arguments.clone());
                    }
                }
            }
        }
        // What another crate's code the call runs may run of this crate's
        // impls (`Iterator::next` under `take`, under a generic `it.any(..)`).
        let reentered = if let (true, ty::FnDef(callee, fn_args)) = (outside, fn_ty.kind()) {
            self.reentries(*callee, tcx.instantiate_bound_regions_with_erased(*fn_args))
        } else {
            Vec::new()
        };
        if !reentered.is_empty() {
            // A closure it is passed may be called with what they return
            // (`w.take(3).any(|u| ..)`).
            for (_, closure) in &closures {
                let mut returned = Src::default();
                returned.calls.insert(at);
                self.edges.closure_params.push((*closure, returned));
            }
        }
        match target {
            Target::One(callee) => {
                let callee = def_key(callee);
                for (index, src) in srcs.iter().enumerate() {
                    if !src.is_empty() {
                        let key = (callee, index_key(index));
                        self.edges.params.push((key, src.clone()));
                    }
                }
                self.edges.calls.push(CallSite {
                    at,
                    callees: vec![callee],
                    resolved: true,
                    args: srcs.clone(),
                    writes,
                    closures,
                });
            }
            Target::Many(_) | Target::Outside => {
                for body in &bodies {
                    for (index, src) in srcs.iter().enumerate() {
                        if !src.is_empty() {
                            let key = (def_key(*body), index_key(index));
                            self.edges.params.push((key, src.clone()));
                        }
                    }
                }
                self.write_through(&writes, &others);
                let callees: Vec<u32> = bodies
                    .iter()
                    .chain(&reentered)
                    .map(|body| def_key(*body))
                    .collect();
                if !callees.is_empty() {
                    self.edges.calls.push(CallSite {
                        at,
                        callees,
                        resolved: false,
                        args: srcs.clone(),
                        writes: Vec::new(),
                        closures,
                    });
                }
            }
        }
        let ty::FnDef(callee, fn_args) = fn_ty.kind() else {
            return;
        };
        let span = thir[id].span;
        // The comparison `assert_eq!` / `assert_ne!` write (a panic), and the
        // one a builtin derive writes (field by field, the same variant).
        if from_assertion(tcx, span) || from_builtin_derive(tcx, span) {
            return;
        }
        // A comparison none of whose operands is computed from anything that
        // can carry a variant (two strings, two parameters' fields read as
        // numbers) is not a sink, and not counted as one.
        let src = others(usize::MAX);
        if src.is_empty() {
            return;
        }
        if let Some((what, enums)) = self.comparison(
            *callee,
            tcx.instantiate_bound_regions_with_erased(*fn_args),
            !outside,
        ) {
            self.edges.sinks.push(Sink {
                span,
                what,
                enums,
                src,
            });
        }
    }

    /// A comparison passed as a value (`fold(Ty::A, Ord::max)`,
    /// `sort_by(Ord::cmp)`): the callee compares with it what the call's other
    /// arguments hand it, as the closure `|a, b| a.max(b)` would, and a
    /// function of this crate what it calls its parameter with (verifier
    /// land-clean-r1: the closure was refused, the path passed).
    fn passed_comparison(
        &mut self,
        arg: ExprId,
        index: usize,
        bodies: &[LocalDefId],
        others: &impl Fn(usize) -> Src,
    ) {
        let tcx = self.tcx;
        let core = &self.thir[self.core(arg)];
        let (ExprKind::ZstLiteral { .. }, ty::FnDef(item, item_args)) =
            (&core.kind, core.ty.kind())
        else {
            return;
        };
        if from_assertion(tcx, core.span) || from_builtin_derive(tcx, core.span) {
            return;
        }
        let followed = body_fn(tcx, *item).is_some();
        let Some((what, enums)) = self.comparison(
            *item,
            tcx.instantiate_bound_regions_with_erased(*item_args),
            followed,
        ) else {
            return;
        };
        let mut src = others(index);
        for body in bodies {
            src.called_with.insert((def_key(*body), index_key(index)));
        }
        if src.is_empty() {
            return;
        }
        self.edges.sinks.push(Sink {
            span: core.span,
            what: format!("{what}, passed as a value,"),
            enums,
            src,
        });
    }

    /// The expression an argument (or a callee) is, under the scopes, borrows
    /// and moves that wrap it -- not under a coercion to a function pointer.
    fn core(&self, mut id: ExprId) -> ExprId {
        while let ExprKind::Scope { value: inner, .. }
        | ExprKind::Borrow { arg: inner, .. }
        | ExprKind::ValueExpr { source: inner } = self.thir[id].kind
        {
            id = inner;
        }
        id
    }

    /// The closures of this crate an argument holds, read off its type before
    /// the borrows and coercions that pass it erase them (`&|u| ..` passed as
    /// a `&dyn Fn`, `Box::new(|u| ..)` as a `Box<dyn Fn>`).
    fn closures_in(&self, id: ExprId) -> Vec<LocalDefId> {
        let expr = &self.thir[id];
        let mut out = closures_of(expr.ty);
        if let ExprKind::Scope { value: inner, .. }
        | ExprKind::PointerCoercion { source: inner, .. }
        | ExprKind::Borrow { arg: inner, .. }
        | ExprKind::ValueExpr { source: inner }
        | ExprKind::Deref { arg: inner } = &expr.kind
        {
            for closure in self.closures_in(*inner) {
                if !out.contains(&closure) {
                    out.push(closure);
                }
            }
        }
        out
    }

    /// A callee whose body is not followed: an argument it can write through
    /// takes what the call's other arguments carry.
    fn write_through(&mut self, writes: &[(u32, Var)], others: &impl Fn(usize) -> Src) {
        for (index, var) in writes {
            let src = others(usize::try_from(*index).unwrap_or(usize::MAX));
            if !src.is_empty() {
                self.edges.vars.push((*var, src));
            }
        }
    }
}

/// What the resolution knows of a node: the variants named in its own body it
/// may carry, and the parameters of the crate's functions it may be computed
/// from -- whose variants, from every call, [`Vals::resolved`] reads where a
/// value is compared, so one call's argument never reaches another call's
/// result.
#[derive(Clone, Default)]
struct Val {
    named: Named,
    params: BTreeSet<Param>,
}

impl Val {
    fn absorb(&mut self, other: &Self) {
        self.name(&other.named);
        self.params.extend(other.params.iter().copied());
    }

    fn name(&mut self, named: &Named) {
        for (enum_def, witness) in named {
            self.named
                .entry(*enum_def)
                .or_insert_with(|| witness.clone());
        }
    }
}

/// The value of every node, to a fixed point.
#[derive(Default)]
struct Vals {
    vars: BTreeMap<Var, Val>,
    closure_params: BTreeMap<u32, Val>,
    closure_results: BTreeMap<u32, Val>,
    closure_writes: BTreeMap<u32, Val>,
    /// A parameter's variant, from what its calls pass (its own position is
    /// what [`Src::params`] carries).
    params: BTreeMap<Param, Val>,
    results: BTreeMap<u32, Val>,
    writes: BTreeMap<Param, Val>,
    calls: BTreeMap<Call, Val>,
    /// What a parameter that is called back (`f(x)`) is called with.
    callbacks: BTreeMap<Param, Val>,
    /// Every gated variant the crate names ([`Edges::named`]).
    every: Named,
}

/// Adds `add` to the node `key` of `map`; whether it grew.
fn grow<K: Ord>(map: &mut BTreeMap<K, Val>, key: K, add: Val) -> bool {
    if add.named.is_empty() && add.params.is_empty() {
        return false;
    }
    let slot = map.entry(key).or_default();
    let mut grew = false;
    for (enum_def, witness) in add.named {
        if let std::collections::btree_map::Entry::Vacant(vacant) = slot.named.entry(enum_def) {
            vacant.insert(witness);
            grew = true;
        }
    }
    for param in add.params {
        grew |= slot.params.insert(param);
    }
    grew
}

impl Vals {
    fn eval(&self, src: &Src) -> Val {
        let mut out = Val {
            named: src.named.clone(),
            params: src.params.clone(),
        };
        if let Some(witness) = &src.every {
            for enum_def in self.every.keys() {
                out.named
                    .entry(*enum_def)
                    .or_insert_with(|| witness.clone());
            }
        }
        let parts = src
            .vars
            .iter()
            .filter_map(|var| self.vars.get(var))
            .chain(
                src.closure_params
                    .iter()
                    .filter_map(|def| self.closure_params.get(def)),
            )
            .chain(
                src.closure_results
                    .iter()
                    .filter_map(|def| self.closure_results.get(def)),
            )
            .chain(
                src.closure_writes
                    .iter()
                    .filter_map(|def| self.closure_writes.get(def)),
            )
            .chain(src.calls.iter().filter_map(|call| self.calls.get(call)));
        for part in parts {
            out.absorb(part);
        }
        for def in &src.fn_items {
            if let Some(result) = self.results.get(def) {
                out.name(&result.named);
            }
        }
        for param in &src.called_with {
            if let Some(with) = self.callbacks.get(param) {
                out.absorb(with);
            }
        }
        if let Some(mask) = &src.mask {
            out.named.retain(|enum_def, _| mask.contains(enum_def));
        }
        out
    }

    /// The variants a value may carry: its own, and those every call passes
    /// the parameters it may be.
    fn resolved(&self, val: &Val) -> Named {
        let mut named = val.named.clone();
        for param in &val.params {
            if let Some(from) = self.params.get(param) {
                for (enum_def, witness) in &from.named {
                    named.entry(*enum_def).or_insert_with(|| witness.clone());
                }
            }
        }
        named
    }

    /// What one call returns, what it leaves in each variable it passes by a
    /// writable reference, and what it hands each closure it passes: the
    /// variants the callee names in them, and what it hands on of THIS call's
    /// arguments (never another call's: those are its parameters' own).
    fn call(&mut self, call: &CallSite) -> bool {
        let mut changed = false;
        for callee in &call.callees {
            changed |= self.call_of(call, *callee);
        }
        changed
    }

    fn call_of(&mut self, call: &CallSite, callee: u32) -> bool {
        let passed = |vals: &Self, from: Option<&Val>, skip: Option<u32>| {
            let mut out = Val::default();
            let Some(from) = from else {
                return out;
            };
            for (index, arg) in call.args.iter().enumerate() {
                let position = index_key(index);
                if call.resolved
                    && Some(position) != skip
                    && from.params.contains(&(callee, position))
                {
                    out.absorb(&vals.eval(arg));
                }
            }
            out.name(&from.named);
            out
        };
        let result = passed(self, self.results.get(&callee), None);
        let mut changed = grow(&mut self.calls, call.at, result);
        for (position, var) in &call.writes {
            let wrote = passed(self, self.writes.get(&(callee, *position)), Some(*position));
            changed |= grow(&mut self.vars, *var, wrote);
        }
        for (position, closure) in &call.closures {
            let fed = passed(
                self,
                self.callbacks.get(&(callee, *position)),
                Some(*position),
            );
            changed |= grow(&mut self.closure_params, *closure, fed);
        }
        changed
    }
}

/// Resolves every comparison of the compilation once all bodies are scanned,
/// to a fixed point. Returns a refusal for every comparison that reaches a
/// named variant.
fn resolve(edges: &Edges) -> Vec<Refusal> {
    let mut vals = Vals {
        every: edges.named.clone(),
        ..Vals::default()
    };
    loop {
        let mut changed = false;
        for (var, src) in &edges.vars {
            let add = vals.eval(src);
            changed |= grow(&mut vals.vars, *var, add);
        }
        for (def, src) in &edges.closure_params {
            let add = vals.eval(src);
            changed |= grow(&mut vals.closure_params, *def, add);
        }
        for (def, src) in &edges.closure_writes {
            let add = vals.eval(src);
            changed |= grow(&mut vals.closure_writes, *def, add);
        }
        for (def, src) in &edges.closure_results {
            let add = vals.eval(src);
            changed |= grow(&mut vals.closure_results, *def, add);
        }
        for (param, src) in &edges.params {
            // A parameter takes its callers' variants, theirs through their
            // own parameters included; the position it is, is its own.
            let add = Val {
                named: vals.resolved(&vals.eval(src)),
                params: BTreeSet::new(),
            };
            changed |= grow(&mut vals.params, *param, add);
        }
        for (arity, args) in &edges.pointer_calls {
            let mut all = Val::default();
            for arg in args {
                all.absorb(&vals.eval(arg));
            }
            for closure in &edges.erased {
                changed |= grow(&mut vals.closure_params, *closure, all.clone());
            }
            for (def, count) in &edges.reified {
                if count != arity {
                    continue;
                }
                for (index, arg) in args.iter().enumerate() {
                    let add = Val {
                        named: vals.resolved(&vals.eval(arg)),
                        params: BTreeSet::new(),
                    };
                    changed |= grow(&mut vals.params, (*def, index_key(index)), add);
                }
            }
        }
        for arguments in &edges.erased_calls {
            let with = vals.eval(arguments);
            for closure in &edges.erased {
                changed |= grow(&mut vals.closure_params, *closure, with.clone());
            }
        }
        for (receiver, arguments) in &edges.callbacks {
            let called = vals.eval(receiver).params;
            let with = vals.eval(arguments);
            for param in called {
                changed |= grow(&mut vals.callbacks, param, with.clone());
            }
        }
        for (passed, param) in &edges.forwards {
            let Some(with) = vals.callbacks.get(param).cloned() else {
                continue;
            };
            for called in vals.eval(passed).params {
                changed |= grow(&mut vals.callbacks, called, with.clone());
            }
        }
        for (def, src) in &edges.results {
            let add = vals.eval(src);
            changed |= grow(&mut vals.results, *def, add);
        }
        for (param, src) in &edges.writes {
            let add = vals.eval(src);
            changed |= grow(&mut vals.writes, *param, add);
        }
        for call in &edges.calls {
            changed |= vals.call(call);
        }
        if !changed {
            break;
        }
    }
    edges
        .sinks
        .iter()
        .filter_map(|sink| {
            let named = vals.resolved(&vals.eval(&sink.src));
            let (at, what) = named
                .iter()
                .find_map(|(enum_def, witness)| {
                    sink.enums
                        .as_ref()
                        .is_none_or(|enums| enums.contains(enum_def))
                        .then_some(witness)
                })?
                .clone();
            Some(Refusal {
                span: sink.span,
                why: format!(
                    "{} compares a value built from {what} -- a variant told apart by value is {CATCH_ALL}: the comparison's other outcome stands for every other variant and compiles unchanged when the enum gains one; name the variants in a `match`",
                    sink.what
                ),
                told: Some(at),
            })
        })
        .collect()
}

/// The scan of one body: every pattern set it holds.
fn scan_body<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, thir: &Thir<'tcx>, root: ExprId) {
    let mut read = BTreeSet::new();
    let mut refused = Vec::new();
    let (mut sets, mut derived) = (0, 0);
    let mut set = |read: &mut BTreeSet<usize>, pats: &[&Pat<'tcx>], failure: Option<&str>| {
        let mut alts = Alts {
            tcx,
            next_alt: 0,
            tells: Vec::new(),
            catches: Vec::new(),
            unmodeled: Vec::new(),
            read,
        };
        for pat in pats {
            let alt = alts.fresh();
            alts.walk(pat, &[], alt);
        }
        if let (Some(what), Some(first)) = (failure, pats.first()) {
            let alt = alts.fresh();
            alts.catch(&[], alt, first.span, what.to_string());
        }
        sets += 1;
        refused.extend(alts.verdicts());
    };
    for expr in thir.exprs.iter() {
        if let ExprKind::Match { arms, .. } = &expr.kind {
            let pats: Vec<&Pat<'tcx>> = arms.iter().map(|arm| &*thir[*arm].pattern).collect();
            if from_builtin_derive(tcx, expr.span) {
                derived += 1;
                // Read, not judged: the walk below must not call them unread.
                pats.iter().for_each(|pat| mark_read(&mut read, pat));
                continue;
            }
            set(&mut read, &pats, None);
        } else if let ExprKind::Let { pat, .. } = &expr.kind {
            let what = "the failure branch of this `if let` / `while let` / `let` chain";
            set(&mut read, &[&**pat], Some(what));
        }
    }
    for stmt in thir.stmts.iter() {
        match &stmt.kind {
            StmtKind::Let {
                pattern,
                else_block,
                ..
            } => {
                let failure = else_block.map(|_| "the `else` of this `let .. else`");
                set(&mut read, &[&**pattern], failure);
            }
            StmtKind::Expr { .. } => {}
        }
    }
    for param in thir.params.iter() {
        if let Some(pat) = &param.pat {
            set(&mut read, &[&**pat], None);
        }
    }
    let mut unread = Unread {
        thir,
        read: &read,
        missed: Vec::new(),
    };
    unread.visit_expr(&thir[root]);
    for span in unread.missed {
        refused.push(Refusal {
            span,
            why: "a pattern in a construct this scan does not read (the compiler's own THIR walk reached it) -- refused, not judged".to_string(),
            told: None,
        });
    }
    let mut flow = Flow {
        tcx,
        def,
        thir,
        holds: Holds::new(tcx, def),
        memo: vec![None; thir.exprs.len()],
        breaks: None,
        edges: Edges::new(),
        refused: Vec::new(),
    };
    flow.run(def, root);
    refused.extend(flow.refused);
    let patterns = read.len();
    found(|found| {
        found.refused.extend(refused);
        found.edges.extend(flow.edges);
        found.patterns += patterns;
        found.sets += sets;
        found.derived += derived;
    });
}

fn mark_read(read: &mut BTreeSet<usize>, pat: &Pat<'_>) {
    read.insert(std::ptr::from_ref(pat) as usize);
    visit_subpatterns(pat, &mut |sub| mark_read(read, sub));
}

/// Each direct subpattern of `pat`.
fn visit_subpatterns<'a, 'tcx>(pat: &'a Pat<'tcx>, each: &mut impl FnMut(&'a Pat<'tcx>)) {
    match &pat.kind {
        PatKind::Binding {
            subpattern: Some(sub),
            ..
        }
        | PatKind::Deref {
            subpattern: sub, ..
        }
        | PatKind::DerefPattern {
            subpattern: sub, ..
        }
        | PatKind::Guard {
            subpattern: sub, ..
        } => each(sub),
        PatKind::Variant { subpatterns, .. } | PatKind::Leaf { subpatterns } => {
            subpatterns.iter().for_each(|field| each(&field.pattern));
        }
        PatKind::Slice {
            prefix,
            slice,
            suffix,
        }
        | PatKind::Array {
            prefix,
            slice,
            suffix,
        } => prefix
            .iter()
            .chain(slice.as_deref())
            .chain(suffix.iter())
            .for_each(each),
        PatKind::Or { pats } => pats.iter().for_each(each),
        PatKind::Binding {
            subpattern: None, ..
        }
        | PatKind::Missing
        | PatKind::Wild
        | PatKind::Constant { .. }
        | PatKind::Range(_)
        | PatKind::Never
        | PatKind::Error(_) => {}
    }
}

// ── THE DRIVER ──────────────────────────────────────────────────────────────

struct Driver {
    /// This run's [`RUN_VAR`], recorded in the unit's dep-info.
    run: Option<String>,
    /// Tests only: compile this source instead of the input file, and collect
    /// the refusals as `LINE: why` instead of emitting them.
    fixture: Option<String>,
    collect: bool,
    /// Set once the analysis is over: the fixture compiled.
    collected: Option<Vec<String>>,
}

impl Callbacks for Driver {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, providers| {
            let _ = ORIGINAL.set(providers.queries.thir_body);
            providers.queries.thir_body = thir_body;
        });
        if let Some(src) = self.fixture.take() {
            config.input = rustc_session::config::Input::Str {
                name: rustc_span::FileName::Custom("fixture".to_string()),
                input: src,
            };
        }
    }

    fn after_crate_root_parsing(
        &mut self,
        compiler: &Compiler,
        _: &mut rustc_ast::Crate,
    ) -> Compilation {
        found(|found| *found = Found::new());
        let run = self.run.as_deref().map(Symbol::intern);
        compiler
            .sess
            .env_depinfo
            .lock()
            .insert((Symbol::intern(RUN_VAR), run));
        Compilation::Continue
    }

    fn after_analysis(&mut self, _: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        // A body no pass lowered (nothing built its MIR) is lowered now.
        for def in tcx.hir_body_owners() {
            if !found(|found| found.scanned.contains(&def.local_def_index.as_u32())) {
                let _ = tcx.thir_body(def);
            }
        }
        let found = take_found();
        let unscanned: Vec<LocalDefId> = tcx
            .hir_body_owners()
            .filter(|def| !found.scanned.contains(&def.local_def_index.as_u32()))
            .collect();
        let mut refused = found.refused;
        refused.extend(resolve(&found.edges));
        for def in unscanned {
            refused.push(Refusal {
                span: tcx.def_span(def),
                why: "a body the compiler never lowered to THIR, so this scan never read it -- refused, not judged".to_string(),
                told: None,
            });
        }
        let crate_name = tcx.crate_name(rustc_span::def_id::LOCAL_CRATE);
        eprintln!(
            "lint-types: scanned crate `{crate_name}` test={} bodies={} pattern-sets={} patterns={} derived={} comparisons={} types={} types-past-limit={} refused={}",
            tcx.sess.is_test_crate(),
            found.scanned.len(),
            found.sets,
            found.patterns,
            found.derived,
            found.edges.sinks.len(),
            found.held_enums.len(),
            found.capped,
            refused.len()
        );
        if self.collect {
            let source_map = tcx.sess.source_map();
            let lines = refused.iter().map(|refusal| {
                let line = source_map.lookup_char_pos(refusal.span.lo()).line;
                format!("{line}: {}", refusal.why)
            });
            self.collected = Some(lines.collect());
            return Compilation::Stop;
        }
        for refusal in refused {
            let mut diag = tcx.dcx().struct_span_err(refusal.span, refusal.why);
            if let Some(told) = refusal.told {
                diag = diag.with_span_note(told, "told apart here");
            }
            diag.emit();
        }
        Compilation::Continue
    }
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().collect();
    // Cargo runs a workspace wrapper as `<wrapper> <rustc> <args>`: this
    // process is the compiler, so the rustc it names is dropped.
    let names_rustc = args.get(1).is_some_and(|arg| {
        std::path::Path::new(arg)
            .file_stem()
            .is_some_and(|stem| stem == "rustc" || stem == "trustc")
    });
    if names_rustc {
        args.remove(1);
    }
    let mut driver = Driver {
        run: std::env::var(RUN_VAR).ok(),
        fixture: None,
        collect: false,
        collected: None,
    };
    rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut driver))
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::process::ExitCode;

    use super::{Driver, CATCH_ALL};

    fn refusals(src: &str) -> Vec<String> {
        refusals_in(src, "2021")
    }

    fn refusals_in(src: &str, edition: &str) -> Vec<String> {
        refusals_with(src, edition, "fixture", &[])
    }

    /// The refusals over `src`, compiled as the crate `name` with `extra`
    /// arguments.
    fn refusals_with(src: &str, edition: &str, name: &str, extra: &[String]) -> Vec<String> {
        let mut args: Vec<String> = [
            "lint-types",
            "fixture.rs",
            "--crate-type=lib",
            "--cap-lints=allow",
            "--edition",
            edition,
        ]
        .iter()
        .map(|arg| arg.to_string())
        .collect();
        args.push(format!("--crate-name={name}"));
        args.extend(extra.iter().cloned());
        let mut driver = Driver {
            run: None,
            fixture: Some(src.to_string()),
            collect: true,
            collected: None,
        };
        let _ = rustc_driver::catch_with_exit_code(|| {
            rustc_driver::run_compiler(&args, &mut driver);
        });
        driver
            .collected
            .unwrap_or_else(|| panic!("the fixture did not compile:\n{src}"))
    }

    /// A directory of this test's own under the temporary directory, empty.
    fn scratch(test: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("lint-types-{}-{test}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("a scratch directory");
        dir
    }

    /// Compiles `src` as the library crate `name` into `dir` (its metadata
    /// only, which is what a dependent's `--extern` reads), through the driver
    /// with the scan's refusals emitted, and returns the file.
    fn dependency(src: &str, name: &str, dir: &Path) -> PathBuf {
        let args: Vec<String> = [
            "lint-types",
            "dependency.rs",
            "--crate-type=lib",
            "--edition=2021",
            "--emit=metadata",
            "--out-dir",
        ]
        .iter()
        .map(|arg| arg.to_string())
        .chain([dir.display().to_string(), format!("--crate-name={name}")])
        .collect();
        let mut driver = Driver {
            run: None,
            fixture: Some(src.to_string()),
            collect: false,
            collected: None,
        };
        let code = rustc_driver::catch_with_exit_code(|| {
            rustc_driver::run_compiler(&args, &mut driver);
        });
        assert_eq!(
            code,
            ExitCode::SUCCESS,
            "the dependency `{name}` did not compile"
        );
        let rmeta = dir.join(format!("lib{name}.rmeta"));
        assert!(rmeta.is_file(), "no {}", rmeta.display());
        rmeta
    }

    /// The fixture's own enum stands in for trust-ir's: the crate being
    /// compiled is gated too.
    /// `no_std`: each fixture loads core's metadata, not std's (a third of the
    /// time per compile).
    const TY: &str = "#![no_std]\n#[derive(Clone, Copy, PartialEq, Eq, Debug)]\npub enum Ty { A, B(u8), C }\n#[derive(Clone, Copy, PartialEq, Eq, Debug)]\npub struct Key { pub kind: Ty, pub id: u8 }\npub const EMPTY: Key = Key { kind: Ty::A, id: 0 };\npub const SOME_A: Option<Ty> = Some(Ty::A);\n";

    #[track_caller]
    fn refused(body: &str, needle: &str) {
        let src = format!("{TY}{body}\n");
        let found = refusals(&src);
        assert!(
            found.iter().any(|f| f.contains(needle)),
            "expected a refusal naming {needle:?} in\n{body}\ngot {found:?}"
        );
    }

    #[track_caller]
    fn passes(body: &str) {
        let src = format!("{TY}{body}\n");
        let found = refusals(&src);
        assert!(
            found.is_empty(),
            "expected no refusal in\n{body}\ngot {found:?}"
        );
    }

    #[track_caller]
    fn catch_all(body: &str) {
        refused(body, CATCH_ALL);
    }

    // ── the whole arm is judged like any other place ─────────────────────────

    #[test]
    fn a_whole_arm_catch_all_beside_a_variant_is_refused() {
        catch_all("pub fn f(t: Ty) -> u8 { match t { Ty::A => 1, _ => 2 } }");
        catch_all(
            "pub fn f(t: &Ty) -> u8 { match t { Ty::A => 1, other => { let _ = other; 2 } } }",
        );
        // verifier r10: an attribute on an arm turned clippy's match lints off.
        catch_all("pub fn f(t: Ty) -> u8 { match t { Ty::A => 1, #[allow(unused)] Ty::B(_) => 2, _ => 3 } }");
        // verifier r10: under `x @`, and behind `&` in an or-pattern.
        catch_all("pub fn f(t: &Ty) -> u8 { match t { Ty::A => 1, _x @ &_ => 2 } }");
        catch_all("pub fn f(t: &Ty) -> u8 { match t { Ty::A => 1, _x @ (Ty::B(_) | _) => 2 } }");
        catch_all("pub fn f(t: &Ty) -> u8 { match t { &Ty::A => 1, &Ty::B(_) | &_ => 2 } }");
    }

    // ── below the top ────────────────────────────────────────────────────────

    #[test]
    fn a_catch_all_below_the_top_is_refused() {
        // verifier r9c
        catch_all("pub fn f(t: Option<Ty>) -> u8 { match t { Some(Ty::A) => 1, Some(_) => 2, None => 3 } }");
        catch_all("pub fn f(t: Ty) -> u8 { match (t, ()) { (Ty::A, ()) => 1, (_, ()) => 2 } }");
        catch_all("pub fn f(t: (Ty, Ty)) -> u8 { match t { (Ty::A, Ty::B(_)) => 1, _ => 2 } }");
        // verifier r10: a field counted from the end is the field it is.
        catch_all("pub fn f(t: &Ty) -> u8 { match ((), t) { (.., Ty::A) => 1, (_, _) => 2 } }");
        catch_all("pub fn f(t: (u8, u8, Ty)) -> u8 { match t { (.., Ty::A) => 1, (_, _, other) => { let _ = other; 2 } } }");
        // an element counted from the end may be one counted from the start
        catch_all("pub fn f(t: &[Ty]) -> u8 { match t { [.., Ty::A] => 1, [_] => 2, [_, .., Ty::B(_) | Ty::C] => 3, [] => 4 } }");
        catch_all(
            "pub fn f(t: &[Ty]) -> u8 { match t { [Ty::A, ..] => 1, [_, ..] => 2, [] => 3 } }",
        );
        // a rest stands for every element past the ones its pattern names
        catch_all("pub fn f(t: &[Ty]) -> usize { match t { [Ty::A, rest @ ..] => rest.len(), [Ty::B(_) | Ty::C, Ty::B(_), ..] => 2, [Ty::B(_) | Ty::C, ..] | [] => 3 } }");
        // a field a pattern leaves out
        catch_all(
            "pub fn f(k: Key) -> u8 { match k { Key { kind: Ty::A, .. } => 1, Key { .. } => 2 } }",
        );
        catch_all("pub fn f(t: (Ty, u8)) -> u8 { match t { (Ty::A, 0) => 1, (..) => 2 } }");
    }

    // ── a name is what rustc resolved it to ─────────────────────────────────

    #[test]
    fn a_named_constant_is_the_variants_it_denotes() {
        // verifier r10b: rc=0 on the real check before this scan.
        catch_all("pub fn f(k: Key) -> u8 { match k { EMPTY => 1, _ => 3 } }");
        catch_all("pub fn f(o: Option<Ty>) -> u8 { match o { SOME_A => 1, None => 2, _ => 3 } }");
        catch_all(
            "pub fn f(o: Option<Ty>) -> u8 { match o { SOME_A => 1, Some(_) => 3, None => 2 } }",
        );
        catch_all("pub fn f(k: Key) -> u8 { match k { EMPTY => 1, Key { kind: _, id } => id } }");
        catch_all("const 甲: Ty = Ty::A;\npub fn f(o: Option<Ty>) -> u8 { match o { Some(甲) => 1, Some(_) => 3, None => 2 } }");
        catch_all("#[allow(non_upper_case_globals)]\nconst a_ty: Ty = Ty::A;\npub fn f(o: Option<Ty>) -> u8 { match o { Some(a_ty) => 1, Some(_) => 3, None => 2 } }");
        // verifier r11v: rc=0 on the real check before the typed scan -- a
        // constant of a slice or a tuple type is the elements it denotes.
        catch_all("const ONLY_A: &[Ty] = &[Ty::A];\npub fn f(s: &[Ty]) -> u8 { match s { ONLY_A => 1, _ => 3 } }");
        catch_all("const PAIR: (Ty, u8) = (Ty::A, 0);\npub fn f(t: Ty) -> u8 { match (t, 1u8) { PAIR => 1, (_, n) => n } }");
    }

    #[test]
    fn a_binding_is_a_binding_whatever_its_case() {
        catch_all("#[allow(non_snake_case)]\npub fn f(o: Option<Ty>) -> u8 { match o { Some(Ty::A) => 1, Some(値) => { let _ = 値; 3 } None => 2 } }");
        catch_all("#[allow(non_snake_case)]\npub fn f(o: Option<Ty>) -> u8 { match o { Some(Ty::A) => 1, Some(Other) => { let _ = Other; 3 } None => 2 } }");
    }

    #[test]
    fn self_and_an_alias_are_the_type_they_name() {
        // verifier r10b: `Self` and an alias were other constructors to the syn scan.
        catch_all("impl Key { pub fn f(self) -> u8 { match self { Key { kind: Ty::A, .. } => 1, Self { kind: _, .. } => 3 } } }");
        catch_all("pub struct W(pub Ty);\nimpl W { pub fn f(self) -> u8 { match self { Self(Ty::A) => 1, W(_) => 3 } } }");
        catch_all("type K = Key;\npub fn f(k: Key) -> u8 { match k { K { kind: Ty::A, .. } => 1, Key { kind: _, .. } => 3 } }");
    }

    // ── every pattern the compiler builds ───────────────────────────────────

    #[test]
    fn a_refutable_let_has_a_catch_all_failure_branch() {
        catch_all("pub fn f(t: Ty) -> u8 { if let Ty::B(n) = t { n } else { 0 } }");
        catch_all("pub fn f(t: Ty) -> u8 { let Ty::B(n) = t else { return 0 }; n }");
        catch_all("pub fn f(ts: &[Ty]) -> u8 { let mut it = ts.iter(); let mut n = 0; while let Some(Ty::A) = it.next() { n += 1; } n }");
        let chain = format!("{TY}pub fn f(t: Ty, u: Option<u8>) -> u8 {{ if let Some(n) = u && let Ty::B(m) = t {{ n + m }} else {{ 0 }} }}\n");
        let found = refusals_in(&chain, "2024");
        assert!(
            found.iter().any(|f| f.contains(CATCH_ALL)),
            "a `let` chain: {found:?}"
        );
        // std's enums are not gated: `Option` itself tells nothing apart here.
        passes("pub fn f(u: Option<u8>) -> u8 { if let Some(n) = u { n } else { 0 } }");
        passes("pub fn f(u: Option<Ty>) -> Ty { let Some(t) = u else { return Ty::C }; t }");
    }

    #[test]
    fn a_match_a_macro_writes_is_scanned() {
        catch_all("pub fn f(t: Ty) -> bool { matches!(t, Ty::A) }");
        catch_all("macro_rules! hide { ($t:expr) => { match $t { Ty::A => 1, _ => 2 } } }\npub fn f(t: Ty) -> u8 { hide!(t) }");
    }

    #[test]
    fn every_body_is_scanned() {
        catch_all("pub const C: u8 = match Ty::A { Ty::A => 1, _ => 2 };");
        catch_all("pub fn f() -> [u8; match Ty::A { Ty::A => 1, _ => 2 }] { [0] }");
        catch_all("pub fn f(ts: &[Ty]) -> usize { ts.iter().filter(|t| match t { Ty::A => true, _ => false }).count() }");
        catch_all("pub fn f(t: Ty) -> u8 { let g = |(Ty::A | _): Ty| 1; g(t) }");
        catch_all(
            "#[allow(dead_code)]\nfn never_called(t: Ty) -> u8 { match t { Ty::A => 1, _ => 2 } }",
        );
        catch_all("pub fn f(t: Ty) -> u8 { let (Ty::A | _) = t; 1 }");
    }

    #[test]
    fn a_guard_does_not_make_a_catch_all_safe() {
        catch_all("pub fn f(t: Ty, b: bool) -> u8 { match t { Ty::A => 1, _ if b => 2, Ty::B(_) | Ty::C => 3 } }");
    }

    // ── controls ────────────────────────────────────────────────────────────

    #[test]
    fn named_variants_and_ungated_catch_alls_pass() {
        passes("pub fn f(t: &Ty) -> u8 { match t { Ty::A => 1, Ty::B(n) => *n, Ty::C => 3 } }");
        passes("pub fn f(t: Option<Ty>) -> u8 { match t { Some(Ty::A | Ty::C) => 1, Some(Ty::B(_)) => 2, None => 3 } }");
        // a place nobody tells apart: the whole field is passed on
        passes("pub fn f(o: Option<Ty>) -> Ty { match o { Some(t) => t, None => Ty::C } }");
        passes("pub fn f(k: Key) -> u8 { let Key { kind, id } = k; let _ = kind; id }");
        passes("pub fn f(t: (u8, Option<u8>)) -> u8 { match t { (0, Some(n)) => n, (_, Some(n)) => n + 1, (_, None) => 1 } }");
        passes("pub fn f(t: Result<Option<u8>, u8>) -> u8 { match t { Ok(Some(n)) => n, Ok(_) => 0, Err(e) => e } }");
        passes("pub fn f(n: u8) -> u8 { match n { 0 => 1, 1..=9 => 2, _ => 3 } }");
        passes("pub fn f(s: &str) -> usize { match s { \"a\" => 1, other => other.len() } }");
        passes("pub fn f(s: &[u8]) -> usize { match s { [] => 0, [first, rest @ ..] => usize::from(*first) + rest.len() } }");
        // a rest past the element every alternative names tells nothing apart
        passes("pub fn f(t: &[Ty]) -> usize { match t { [Ty::A, rest @ ..] => rest.len(), [Ty::B(_) | Ty::C, ..] | [] => 0 } }");
        passes("pub fn f(t: Ty) -> u8 { match t { x @ Ty::A => { let _ = x; 1 } Ty::B(_) | Ty::C => 2 } }");
        // a builtin derive's own `_` arm (the fixture's TY derives PartialEq)
        passes("pub fn f(a: Ty, b: Ty) -> bool { a == b }");
    }

    // ── a variant told apart by value (verifier r11v) ────────────────────────

    /// The needle a comparison's refusal carries beside [`CATCH_ALL`].
    const BY_VALUE: &str = "a variant told apart by value";

    /// A refusal by the second rule, which carries both needles.
    #[track_caller]
    fn by_value(body: &str) {
        refused(body, &format!("{BY_VALUE} is {CATCH_ALL}"));
    }

    #[test]
    fn a_comparison_with_a_named_variant_is_refused() {
        // verifier r11v `eq_top`: rc=0 on the real check before this rule.
        by_value("pub fn f(t: Ty) -> u8 { if t == Ty::A { 1 } else { 3 } }");
        by_value("pub fn f(t: &Ty) -> bool { *t != Ty::C }");
        by_value("pub fn f(t: Ty) -> bool { Ty::A == t }");
        by_value("pub fn f(t: Ty) -> bool { t.eq(&Ty::B(1)) }");
        by_value("pub fn f(t: Ty) -> bool { PartialEq::eq(&t, &Ty::A) }");
        by_value("pub fn f(t: Option<Ty>) -> bool { t == Some(Ty::A) }");
        by_value("pub fn f(t: Option<&Ty>) -> bool { t == Some(&Ty::A) }");
        by_value("pub fn f(k: Key) -> bool { k.kind == Ty::A }");
        by_value("pub fn f(k: Key) -> bool { k == Key { kind: Ty::C, id: 0 } }");
        by_value("pub fn f(t: Ty) -> bool { (t, 1) == (Ty::A, 1) }");
        by_value("pub fn f(ts: &[Ty]) -> bool { ts[..1] == [Ty::A] }");
        // a constant is the variants it denotes
        by_value("pub fn f(k: Key) -> bool { k == EMPTY }");
        by_value("pub fn f(o: Option<Ty>) -> bool { o != SOME_A }");
        // an assertion the source writes is a comparison like any other
        by_value("pub fn f(t: Ty) { assert!(t == Ty::A) }");
        // an order is a comparison too
        by_value("#[derive(PartialEq, PartialOrd)]\npub enum O { X, Y }\npub fn f(o: O) -> bool { o < O::Y }");
        by_value("#[derive(PartialEq, Eq, PartialOrd, Ord)]\npub enum O { X, Y }\npub fn f(o: O) -> core::cmp::Ordering { o.cmp(&O::X) }");
    }

    #[test]
    fn a_named_variant_is_followed_through_bindings() {
        // through a `let`, an assignment and a pattern
        by_value("pub fn f(t: Ty) -> bool { let want = Ty::A; t == want }");
        by_value("pub fn f(t: Ty, b: bool) -> bool { let mut want = Ty::C; if b { want = Ty::A; } t == want }");
        by_value("pub fn f(t: Ty) -> bool { if let Some(k) = Some(EMPTY) { k.kind == t } else { false } }");
        // an edge read before the one that names its source: to a fixed point
        by_value("pub fn f(t: Ty, u: Ty) -> bool { let mut b = u; let a = Ty::A; b = a; b == t }");
        // out of a labelled block by a `break`
        by_value("pub fn f(t: Ty, x: Ty, n: u8) -> bool { let w = 'b: { if n == 0 { break 'b Ty::A; } x }; w == t }");
    }

    #[test]
    fn a_named_variant_is_followed_into_closures_and_calls() {
        // into a closure: a capture, a parameter, a result
        by_value(
            "pub fn f(t: Ty) -> bool { let want = Ty::A; let same = |u: Ty| u == want; same(t) }",
        );
        by_value("pub fn f(t: Ty) -> bool { [Ty::A, Ty::C].iter().any(|u| *u == t) }");
        by_value("pub fn f(t: Ty) -> bool { let b = |n: u8| Ty::B(n); b(1) == t }");
        by_value("pub fn f(t: Ty) -> bool { [1u8].into_iter().map(Ty::B).any(|u| u == t) }");
        // through a loop and a library function
        by_value("pub fn f(t: Ty) -> bool { for u in [Ty::A, Ty::C] { if u == t { return true; } } false }");
        by_value("pub fn f(t: Ty) -> bool { core::mem::discriminant(&t) == core::mem::discriminant(&Ty::A) }");
        by_value("pub fn f(t: Ty) -> bool { Some(Ty::A).as_ref() == Some(&t) }");
        by_value("pub fn f(t: Ty, ts: &mut [Ty; 1]) -> bool { ts[0] = Ty::A; ts[0] == t }");
        by_value("extern crate alloc;\npub fn f(t: Ty) -> bool { let mut v = alloc::vec::Vec::new(); v.push(Ty::A); v.contains(&t) }");
        // an overloaded place: `v[0] = ..` through `IndexMut`
        by_value("extern crate alloc;\npub fn f(t: Ty, mut v: alloc::vec::Vec<Ty>) -> bool { v[0] = Ty::A; v.iter().any(|u| *u == t) }");
        // written through a shared reference to a type that is not `Freeze`
        by_value("pub fn f(t: Ty, u: Ty) -> bool { let c = core::cell::Cell::new(u); c.set(Ty::A); c.get() == t }");
        // written through an alias of the variable compared
        by_value("extern crate alloc;\npub fn f(t: Ty) -> bool { let mut v = alloc::vec::Vec::new(); let r = &mut v; r.push(Ty::A); v.contains(&t) }");
        by_value("pub fn f(t: Ty, mut v: [Ty; 2]) -> bool { for x in v.iter_mut() { *x = Ty::A; } v.contains(&t) }");
        by_value("pub fn f(t: Ty, mut v: [Ty; 2]) -> bool { v.iter_mut().for_each(|x| *x = Ty::A); v.contains(&t) }");
        by_value("pub fn f(t: Ty, u: Ty) -> bool { let c = core::cell::Cell::new(u); let r = &c; r.set(Ty::A); c.get() == t }");
        by_value("extern crate alloc;\npub fn f(t: Ty, u: Ty) -> bool { let a = alloc::rc::Rc::new(core::cell::RefCell::new(u)); let b = a.clone(); *b.borrow_mut() = Ty::A; let same = *a.borrow() == t; same }");
        // written through what a call hands back into its receiver
        by_value("pub fn f(t: Ty, u: Ty) -> bool { let c = core::cell::RefCell::new(u); *c.borrow_mut() = Ty::A; let same = *c.borrow() == t; same }");
        by_value("pub fn f(t: Ty, mut v: [Ty; 2]) -> bool { *v.last_mut().unwrap() = Ty::C; v.contains(&t) }");
    }

    #[test]
    fn a_value_of_a_gated_enum_that_reads_no_variable_is_named() {
        // a call that reads no variable returns one fixed variant
        by_value("#[derive(PartialEq, Default)]\npub enum D { #[default] X, Y }\npub fn f(d: D) -> bool { d == D::default() }");
        by_value("fn unit() -> Ty { Ty::C }\npub fn f(t: Ty) -> bool { t == unit() }");
        by_value("fn made(n: u8) -> Ty { Ty::B(n) }\npub fn f(t: &Ty) -> bool { *t != made(1) }");
        by_value("#[derive(PartialEq, Default)]\npub enum D { #[default] X, Y }\n#[derive(Default)]\npub struct S { d: D }\npub fn f(d: D) -> bool { S::default().d == d }");
        by_value("pub fn f(t: Ty) -> bool { EMPTY.kind == t }");
        // only core's assertions are exempt, not a macro of the same name
        by_value("macro_rules! assert_eq { ($a:expr, $b:expr) => { if $a == $b { 1 } else { 0 } } }\npub fn f(t: Ty) -> u8 { assert_eq!(t, Ty::A) }");
    }

    #[test]
    fn a_function_that_compares_what_it_is_given_is_a_comparison() {
        by_value("pub fn f(t: Ty) -> bool { [Ty::A, Ty::C].contains(&t) }");
        by_value("pub fn f(ts: &[Ty]) -> bool { ts.contains(&Ty::A) }");
        by_value("pub fn f(ts: &[Ty]) -> bool { ts.starts_with(&[Ty::A]) }");
        by_value("pub fn f(ts: &[Ty]) -> Option<&[Ty]> { ts.strip_prefix(&[Ty::A][..]) }");
        by_value("pub fn same<T: PartialEq>(a: T, b: T) -> bool { a == b }\npub fn f(t: Ty) -> bool { same(t, Ty::A) }");
        by_value("extern crate alloc;\n#[derive(PartialEq, Eq, PartialOrd, Ord)]\npub enum O { X, Y }\npub fn f(s: &alloc::collections::BTreeSet<O>) -> bool { s.contains(&O::X) }");
    }

    #[test]
    fn a_named_variant_is_followed_into_the_crate_s_own_functions() {
        // into a parameter the callee compares (verifier r11v's `eq_top`, one
        // call away)
        by_value(
            "fn same(a: Ty, b: Ty) -> bool { a == b }\npub fn f(t: Ty) -> bool { same(t, Ty::A) }",
        );
        by_value("impl Key { fn has(&self, t: Ty) -> bool { self.kind == t } }\npub fn f(k: Key) -> bool { k.has(Ty::A) }");
        by_value("impl Ty { fn same(self, o: Ty) -> bool { self == o } }\npub fn f(t: Ty) -> bool { Ty::A.same(t) }");
        // a structure holding one: a constant, a literal, a variable
        by_value("impl Key { fn has(&self, t: Ty) -> bool { self.kind == t } }\npub fn f(t: Ty) -> bool { EMPTY.has(t) }");
        by_value("fn has(k: &Key, t: Ty) -> bool { k.kind == t }\npub fn f(t: Ty, n: u8) -> bool { has(&Key { kind: Ty::C, id: n }, t) }");
        by_value("fn conflicts(ks: &[Key]) -> bool { ks.iter().any(|k| k.kind != ks[0].kind) }\npub fn f(k: Key) -> bool { let ks = [k, Key { kind: Ty::C, id: 1 }]; conflicts(&ks) }");
        by_value("extern crate alloc;\nfn has(v: &alloc::vec::Vec<Ty>, t: &Ty) -> bool { v.contains(t) }\npub fn f(t: Ty) -> bool { has(&alloc::vec![Ty::A, Ty::C], &t) }");
        by_value("fn same(a: Ty, b: Ty) -> bool { a == b }\nfn outer(t: Ty, u: Ty) -> bool { same(t, u) }\npub fn f(t: Ty) -> bool { outer(t, Ty::A) }");
        by_value("fn count(ts: &[Ty], k: Ty) -> usize { ts.iter().filter(|t| **t == k).count() }\npub fn f(ts: &[Ty]) -> usize { count(ts, Ty::C) }");
        // a method of a trait: the impl it resolves to, or every impl of it
        let is = "pub trait Is { fn is(&self, t: Ty) -> bool; }\nimpl Is for Key { fn is(&self, t: Ty) -> bool { self.kind == t } }\n";
        by_value(&format!("{is}pub fn f(k: Key) -> bool {{ k.is(Ty::A) }}"));
        by_value(&format!(
            "{is}pub fn f(k: &dyn Is) -> bool {{ k.is(Ty::A) }}"
        ));
        by_value(&format!(
            "{is}pub fn f<T: Is>(k: &T) -> bool {{ k.is(Ty::A) }}"
        ));
        // a function of this crate passed as a value, or called through a
        // pointer to it
        by_value("fn eq_pair(p: (Ty, Ty)) -> bool { p.0 == p.1 }\npub fn f(t: Ty) -> bool { [(Ty::A, t)].into_iter().any(eq_pair) }");
        by_value("fn same(a: Ty, b: Ty) -> bool { a == b }\npub fn f(t: Ty) -> bool { let p: fn(Ty, Ty) -> bool = same; p(t, Ty::A) }");
        by_value("fn eq_pair(p: (Ty, Ty)) -> bool { p.0 == p.1 }\npub fn f(t: Ty) -> bool { let p: fn((Ty, Ty)) -> bool = eq_pair; [(Ty::A, t)].into_iter().any(p) }");
    }

    #[test]
    fn a_named_variant_is_followed_out_of_the_crate_s_own_functions() {
        // out of its result: what it hands back of the call's own arguments
        by_value("fn pick(d: Ty, n: u8) -> Ty { let _ = n; d }\npub fn f(t: Ty, n: u8) -> bool { pick(Ty::A, n) == t }");
        by_value("fn or(o: Option<Ty>, d: Ty) -> Ty { o.unwrap_or(d) }\npub fn f(o: Option<Ty>, t: Ty) -> bool { or(o, Ty::C) == t }");
        by_value("fn pick(d: Ty, n: u8) -> Ty { let _ = n; d }\nfn twice(d: Ty, n: u8) -> Ty { pick(d, n) }\npub fn f(t: Ty, n: u8) -> bool { twice(Ty::A, n) == t }");
        // through generic code: read off the concrete types at the call
        by_value("fn pick<T>(d: T, n: u8) -> T { let _ = n; d }\npub fn f(t: Ty, n: u8) -> bool { pick(Ty::A, n) == t }");
        by_value("fn put<T>(slot: &mut T, v: T) { *slot = v; }\npub fn f(t: Ty, u: Ty) -> bool { let mut x = u; put(&mut x, Ty::A); x == t }");
        // the variants it names in its result, whatever it computes them from
        // (lane r11b first left these out as the callee's "image" of its
        // input; following them cost one exhaustive `Img::agrees` in the
        // projector)
        by_value("fn made(n: u8) -> Ty { if n == 0 { Ty::C } else { Ty::B(n) } }\npub fn f(t: Ty, n: u8) -> bool { made(n) == t }");
        by_value("fn step(t: Ty, n: u8) -> Ty { match t { Ty::A => Ty::B(n), Ty::B(m) => Ty::B(m + n), Ty::C => Ty::C } }\npub fn f(t: Ty, n: u8) -> bool { step(Ty::A, n) == t }");
        by_value("extern crate alloc;\nfn kinds(wide: bool) -> alloc::vec::Vec<Ty> { let mut v = alloc::vec![Ty::A]; if wide { v.push(Ty::C) } v }\npub fn f(t: Ty, wide: bool) -> bool { kinds(wide).contains(&t) }");
        by_value("fn mk(n: u8) -> Ty { Ty::B(n) }\npub fn f(t: Ty, n: u8) -> bool { mk(n) == t }");
        by_value("fn mk(n: u8) -> Ty { if n > 9 { panic!() } return Ty::B(n); }\npub fn f(t: Ty, n: u8) -> bool { mk(n) == t }");
        by_value("fn mk(n: u8) -> Ty { if n == 0 { Ty::B(1) } else { Ty::B(n) } }\nfn again(n: u8) -> Ty { mk(n) }\npub fn f(t: Ty, n: u8) -> bool { again(n) == t }");
        by_value("fn mk(n: u8) -> Ty { Ty::B(n) }\npub fn f(t: Ty) -> bool { [1u8].into_iter().map(mk).any(|u| u == t) }");
        by_value("fn kinds() -> [Ty; 2] { [Ty::A, Ty::C] }\npub fn f(t: Ty) -> bool { kinds().contains(&t) }");
    }

    #[test]
    fn a_named_variant_is_followed_into_callbacks_and_writes() {
        // what it calls a closure of its caller with
        by_value("fn each_kind(mut f: impl FnMut(Ty)) { f(Ty::A); f(Ty::C); }\npub fn f(t: Ty) -> bool { let mut found = false; each_kind(|k| found |= k == t); found }");
        by_value("fn apply<F: Fn(Ty) -> bool>(f: F, v: Ty) -> bool { f(v) }\npub fn f(t: Ty) -> bool { apply(|u| u == t, Ty::A) }");
        by_value("fn apply(f: &dyn Fn(Ty) -> bool, v: Ty) -> bool { f(v) }\npub fn f(t: Ty) -> bool { apply(&|u| u == t, Ty::A) }");
        by_value("extern crate alloc;\nfn apply(f: alloc::boxed::Box<dyn Fn(Ty) -> bool>, v: Ty) -> bool { f(v) }\npub fn f(t: Ty) -> bool { apply(alloc::boxed::Box::new(move |u| u == t), Ty::A) }");
        by_value("extern crate alloc;\nfn apply<F: Fn(Ty) -> bool>(f: alloc::boxed::Box<F>, v: Ty) -> bool { f(v) }\npub fn f(t: Ty) -> bool { apply(alloc::boxed::Box::new(move |u| u == t), Ty::A) }");
        // a closure erased to a `dyn Fn` kept in a structure, called later
        by_value("extern crate alloc;\npub struct V { f: alloc::boxed::Box<dyn Fn(Ty) -> bool> }\nimpl V { fn run(&self) -> bool { (self.f)(Ty::A) } }\npub fn f(t: Ty) -> bool { let v = V { f: alloc::boxed::Box::new(move |u| u == t) }; v.run() }");
        by_value("pub struct P { f: fn(Ty, Ty) -> bool }\nimpl P { fn run(&self, t: Ty) -> bool { (self.f)(t, Ty::C) } }\nfn same(u: Ty, v: Ty) -> bool { u == v }\npub fn f(t: Ty) -> bool { P { f: same }.run(t) }");
        // what it writes through a reference the caller passes it
        by_value("extern crate alloc;\nfn add(v: &mut alloc::vec::Vec<Ty>, t: Ty) { v.push(t) }\npub fn f(t: Ty) -> bool { let mut v = alloc::vec::Vec::new(); add(&mut v, Ty::A); v.contains(&t) }");
        by_value("extern crate alloc;\nfn fill(v: &mut alloc::vec::Vec<Ty>) { v.push(Ty::A) }\npub fn f(t: Ty) -> bool { let mut v = alloc::vec::Vec::new(); fill(&mut v); v.contains(&t) }");
        by_value("extern crate alloc;\nfn fill(v: &mut alloc::vec::Vec<Ty>, n: u8) { v.push(if n == 0 { Ty::A } else { Ty::B(n) }) }\npub fn f(t: Ty, n: u8) -> bool { let mut v = alloc::vec::Vec::new(); fill(&mut v, n); v.contains(&t) }");
        by_value("fn visit(n: u8, mut f: impl FnMut(Ty)) { f(if n == 0 { Ty::A } else { Ty::B(n) }) }\npub fn f(t: Ty, n: u8) -> bool { let mut hit = false; visit(n, |k| hit |= k == t); hit }");
    }

    /// Probe battery (lane r11b, landing round): each of these passed the
    /// rule as it was first written -- a comparison bound on an impl rather
    /// than on the function, and a method of this crate that another crate
    /// runs, were outside the flow.
    #[test]
    fn a_bound_of_the_impl_or_the_resolved_impl_is_a_comparison() {
        let h =
            "extern crate std;\n#[derive(Clone, Copy, PartialEq, Eq, Hash)]\npub enum H { X, Y }\n";
        // `impl<T: PartialEq, A> Vec<T, A>`: `dedup`
        by_value("extern crate alloc;\npub fn f(t: Ty) -> usize { let mut v = alloc::vec![Ty::A, t]; v.dedup(); v.len() }");
        // `impl<T: Eq + Hash, S: BuildHasher> HashSet<T, S>`: `insert`, `difference`, `is_subset`
        by_value(&format!("{h}pub fn f(h: H) -> bool {{ let mut s: std::collections::HashSet<H> = [H::X].into_iter().collect(); s.insert(h) }}"));
        by_value(&format!("{h}pub fn f(got: &std::collections::HashSet<H>) -> usize {{ let ok: std::collections::HashSet<H> = [H::X].into_iter().collect(); got.difference(&ok).count() }}"));
        by_value(&format!("{h}pub fn f(got: &std::collections::HashSet<H>) -> bool {{ let ok: std::collections::HashSet<H> = [H::X].into_iter().collect(); got.is_subset(&ok) }}"));
        // `impl<K: Eq + Hash, V, S: BuildHasher> HashMap<K, V, S>`: `entry`
        by_value(&format!("{h}pub fn f(h: H) -> u8 {{ let mut m: std::collections::HashMap<H, u8> = [(H::X, 1u8)].into_iter().collect(); *m.entry(h).or_insert(3) }}"));
        // a trait method resolved to an impl whose bounds compare: `map[&k]`
        by_value(&format!("{h}pub fn f(h: H) -> u8 {{ let m: std::collections::HashMap<H, u8> = [(H::X, 1u8)].into_iter().collect(); m[&h] }}"));
    }

    #[test]
    fn a_method_another_crate_runs_may_be_passed_any_value() {
        // `Display::fmt` is called by core's formatting, `Drop::drop` by the
        // compiler: no call of the crate shows what they are passed, so each
        // may be any variant the crate names (here, in `mk`)
        by_value("pub struct R { v: [Ty; 1], w: Ty }\nimpl core::fmt::Display for R { fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result { if self.v.contains(&self.w) { f.write_str(\"a\") } else { f.write_str(\"b\") } } }\npub fn mk(w: Ty) -> R { R { v: [Ty::A], w } }");
        by_value("pub struct G { k: Ty, w: Ty }\nimpl Drop for G { fn drop(&mut self) { if self.k != self.w { self.k = self.w; } } }\npub fn mk(t: Ty) -> G { G { k: Ty::C, w: t } }");
        // what another crate's function runs of this crate's impls hands back
        // what they name: `unwrap_or_default` runs `Default::default` ...
        let cfg = "#[derive(Clone, Copy)]\npub struct Cfg { want: Ty }\nimpl Default for Cfg { fn default() -> Self { Cfg { want: Ty::A } } }\n";
        by_value(&format!(
            "{cfg}pub fn f(o: Option<Cfg>, t: Ty) -> bool {{ o.unwrap_or_default().want == t }}"
        ));
        // ... and `take` / `Take::next` run `Iterator::next`, into a closure
        // and into a `for` loop's binding
        let w = "pub struct W { i: u8 }\nimpl Iterator for W { type Item = Ty; fn next(&mut self) -> Option<Ty> { self.i += 1; if self.i > 2 { None } else { Some(Ty::A) } } }\n";
        by_value(&format!(
            "{w}pub fn f(t: Ty) -> bool {{ W {{ i: 0 }}.take(3).any(|u| u == t) }}"
        ));
        by_value(&format!("{w}pub fn f(t: Ty) -> bool {{ for u in (W {{ i: 0 }}).take(3) {{ if u == t {{ return true; }} }} false }}"));
        // controls: a call that holds no bound on the type runs none of its
        // impls; a comparison trait's impl is judged where it is called; a
        // derived `Clone` hands back only what it was given
        passes(&format!("{cfg}pub fn f(o: Option<Cfg>, t: Ty) -> bool {{ o.unwrap().want == t }}\npub fn g() -> Cfg {{ Cfg::default() }}"));
        passes("pub struct K { k: Ty, n: u8 }\nimpl PartialEq for K { fn eq(&self, o: &K) -> bool { self.k == o.k } }\npub fn f(a: &K, b: &K) -> bool { a == b && a.n > b.n }");
        passes("extern crate alloc;\n#[derive(Clone)]\npub struct H2 { k: Ty }\npub fn f(hs: &[H2], t: Ty) -> bool { let ks: alloc::vec::Vec<Ty> = hs.iter().cloned().map(|h| h.k).collect(); ks[0] == t }");
        passes("pub struct R { v: [Ty; 1] }\nimpl core::fmt::Display for R { fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result { match self.v[0] { Ty::A => f.write_str(\"a\"), Ty::B(_) | Ty::C => f.write_str(\"b\") } } }");
    }

    // ── what a type may hide (verifier land-clean-r1) ───────────────────────

    /// P1: an `impl Trait` held nothing, so a call's result dropped every
    /// variant its body named -- where the concrete `fn kinds() -> [Ty; 2]`
    /// above is refused.
    #[test]
    fn an_impl_trait_result_may_hold_any_variant() {
        let kinds = "fn kinds() -> impl Iterator<Item = Ty> { [Ty::A, Ty::C].into_iter() }\n";
        by_value(&format!(
            "{kinds}pub fn f(t: Ty) -> bool {{ kinds().any(|u| u == t) }}"
        ));
        by_value(&format!("{kinds}pub fn f(t: Ty) -> bool {{ for u in kinds() {{ if u == t {{ return true; }} }} false }}"));
        by_value(&format!("extern crate alloc;\n{kinds}pub fn f(t: Ty) -> bool {{ kinds().collect::<alloc::vec::Vec<Ty>>().contains(&t) }}"));
        by_value("#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]\npub enum O { X, Y }\nfn os() -> impl Iterator<Item = O> { [O::X].into_iter() }\npub fn f(o: O) -> bool { os().chain(core::iter::once(o)).max() == Some(o) }");
        by_value("fn kinds(wide: bool) -> impl Iterator<Item = Ty> { [Ty::A, if wide { Ty::C } else { Ty::A }].into_iter() }\npub fn f(t: Ty, wide: bool) -> bool { kinds(wide).any(|u| u == t) }");
        by_value("fn kinds() -> impl IntoIterator<Item = Ty> { [Ty::A, Ty::C] }\npub fn f(t: Ty) -> bool { kinds().into_iter().any(|u| u == t) }");
        by_value("pub struct M { k: Ty }\nfn ms() -> impl Iterator<Item = M> { [M { k: Ty::A }].into_iter() }\npub fn f(t: Ty) -> bool { ms().any(|m| m.k == t) }");
        by_value("pub struct Tbl { v: [Ty; 1] }\nimpl Tbl { fn iter(&self) -> impl Iterator<Item = &Ty> + '_ { self.v.iter() } }\npub fn f(t: Ty) -> bool { let tb = Tbl { v: [Ty::A] }; let r = tb.iter().any(|u| *u == t); r }");
        by_value("fn mk(n: u8) -> impl Into<Ty> { Ty::B(n) }\npub fn f(t: Ty, n: u8) -> bool { mk(n).into() == t }");
        // an `impl Iterator` hiding this crate's own iterator: its `next`
        let w = "pub struct W { i: u8 }\nimpl Iterator for W { type Item = Ty; fn next(&mut self) -> Option<Ty> { self.i += 1; if self.i > 2 { None } else { Some(Ty::A) } } }\n";
        by_value(&format!("{w}fn w() -> impl Iterator<Item = Ty> {{ W {{ i: 0 }} }}\npub fn f(t: Ty) -> bool {{ w().any(|u| u == t) }}"));
    }

    /// P2: a comparison of a type parameter compared no gated enum, so only a
    /// call whose OWN bounds compare was judged -- not one through a local
    /// trait's supertrait, a trait's default method, a generic function passed
    /// as a value or through a pointer, a generic impl behind `dyn`.
    #[test]
    fn a_comparison_of_a_type_parameter_may_tell_apart_any_variant() {
        by_value("pub trait Tag: Copy + PartialEq {}\nimpl Tag for Ty {}\nfn same<T: Tag>(a: T, b: T) -> bool { a == b }\npub fn f(t: Ty) -> bool { same(t, Ty::A) }");
        by_value("pub trait Tag: Copy + Eq {}\nimpl Tag for Ty {}\nfn has<T: Tag>(xs: &[T], x: T) -> bool { xs.contains(&x) }\npub fn f(t: Ty) -> bool { has(&[Ty::A, Ty::C], t) }");
        by_value("pub trait Kind: Copy + PartialEq { fn is(self, o: Self) -> bool { self == o } }\nimpl Kind for Ty {}\npub fn f(t: Ty) -> bool { t.is(Ty::A) }");
        by_value("pub trait Tag: Copy + PartialEq {}\nimpl Tag for Ty {}\npub struct Set<T: Tag> { v: [T; 1] }\nimpl<T: Tag> Set<T> { fn has(&self, x: T) -> bool { self.v.iter().any(|u| *u == x) } }\npub fn f(t: Ty) -> bool { Set { v: [Ty::A] }.has(t) }");
        by_value("fn same_pair<T: PartialEq>(p: &(T, T)) -> bool { p.0 == p.1 }\npub fn f(t: Ty) -> bool { [(Ty::A, t)].iter().all(same_pair) }");
        by_value("fn same<T: PartialEq>(a: T, b: T) -> bool { a == b }\npub fn f(t: Ty) -> bool { let p: fn(Ty, Ty) -> bool = same; p(t, Ty::A) }");
        by_value("pub trait Same { fn same(&self) -> bool; }\npub struct Pair<T> { a: T, b: T }\nimpl<T: PartialEq> Same for Pair<T> { fn same(&self) -> bool { self.a == self.b } }\npub fn f(t: Ty) -> bool { let p: &dyn Same = &Pair { a: t, b: Ty::A }; p.same() }");
        // a value of a type parameter keeps what it is built from
        by_value("fn mk<T: From<Ty>>(n: u8) -> T { let _ = n; T::from(Ty::A) }\npub fn f(t: Ty, n: u8) -> bool { mk::<Ty>(n) == t }");
        // control: a generic comparison of what its callers computed
        passes("fn same<T: PartialEq>(a: T, b: T) -> bool { a == b }\npub fn f(x: Ty, y: Ty) -> bool { same(x, y) && same(1u8, 2u8) }");
    }

    /// P3: a value erased to a trait object dropped the variants it held.
    #[test]
    fn a_value_erased_to_a_trait_object_keeps_its_variants() {
        by_value("pub trait Same { fn same(&self) -> bool; }\npub struct P2 { a: Ty, b: Ty }\nimpl Same for P2 { fn same(&self) -> bool { self.a == self.b } }\npub fn f(t: Ty) -> bool { let p: &dyn Same = &P2 { a: t, b: Ty::A }; p.same() }");
        by_value("extern crate alloc;\nuse alloc::{boxed::Box, vec, vec::Vec};\npub trait Check { fn ok(&self, t: Ty) -> bool; }\npub struct Want(Ty);\nimpl Check for Want { fn ok(&self, t: Ty) -> bool { self.0 == t } }\npub fn f(t: Ty) -> bool { let cs: Vec<Box<dyn Check>> = vec![Box::new(Want(Ty::C))]; cs.iter().all(|c| c.ok(t)) }");
        // a trait object of this crate's iterator: another crate's `any` runs its `next`
        by_value("extern crate alloc;\npub struct W { i: u8 }\nimpl Iterator for W { type Item = Ty; fn next(&mut self) -> Option<Ty> { self.i += 1; if self.i > 2 { None } else { Some(Ty::A) } } }\npub fn f(t: Ty) -> bool { let mut b: alloc::boxed::Box<dyn Iterator<Item = Ty>> = alloc::boxed::Box::new(W { i: 0 }); b.any(|u| u == t) }");
        // control: an error erased to a trait object, beside an agreement
        passes("extern crate alloc;\npub fn f(t: Ty, u: Ty) -> bool { let e: alloc::boxed::Box<dyn core::error::Error> = alloc::boxed::Box::from(\"x\"); let _ = alloc::string::ToString::to_string(&e); t == u }");
    }

    /// P4: a comparison passed as a value was no sink, where its closure twin
    /// `fold(Ty::A, |a, b| a.max(b))` was.
    #[test]
    fn a_comparison_passed_as_a_value_is_a_comparison() {
        let o = "#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]\npub enum O { X, Y }\n";
        by_value(&format!(
            "{o}pub fn f(os: &[O]) -> O {{ os.iter().copied().fold(O::X, Ord::max) }}"
        ));
        by_value(&format!(
            "{o}pub fn f(o: O) -> Option<O> {{ [O::X, o].into_iter().reduce(Ord::max) }}"
        ));
        by_value(&format!("{o}pub fn f(o: O) -> O {{ let mut v = [O::Y, o]; v.sort_unstable_by(Ord::cmp); v[0] }}"));
        by_value(&format!(
            "{o}pub fn f(o: O) -> Option<O> {{ [O::X, o].into_iter().max_by(Ord::cmp) }}"
        ));
        // passed to a function of this crate: what it calls it with
        by_value(&format!("{o}fn apply<F: Fn(O, O) -> O>(f: F, o: O) -> O {{ f(o, O::Y) }}\npub fn g(o: O) -> O {{ apply(Ord::max, o) }}"));
        // kept where no call shows what it compares, or coerced to a pointer
        // any call through one may run: refused, not judged
        refused(&format!("{o}pub fn f(o: O) -> O {{ let m: fn(O, O) -> O = Ord::max; [O::X, o].into_iter().fold(O::Y, m) }}"), "refused, not judged");
        refused(&format!("{o}fn g(p: fn(O, O) -> O) -> O {{ p(O::X, O::Y) }}\npub fn f() -> O {{ g(Ord::max) }}"), "refused, not judged");
        // controls: values neither of which names a variant
        passes(&format!(
            "{o}pub fn f(os: &[O]) -> Option<O> {{ os.iter().copied().reduce(Ord::max) }}"
        ));
        passes("pub fn f(ns: &[u8]) -> u8 { ns.iter().copied().fold(0, Ord::max) }");
    }

    /// A function value passed on (lane refix1, beside land-clean-r1): a
    /// generic or `dyn` function parameter handed to another crate's function
    /// is called with that call's other arguments, and one handed to this
    /// crate's function is called as its parameter is.
    #[test]
    fn a_function_value_passed_on_is_called_with_what_the_callee_holds() {
        by_value("fn apply<F: Fn(Ty) -> bool>(f: F) -> bool { [Ty::A].iter().copied().any(f) }\npub fn g(t: Ty) -> bool { apply(|u| u == t) }");
        by_value("fn apply(f: &dyn Fn(Ty) -> bool) -> bool { [Ty::A].iter().copied().any(f) }\npub fn g(t: Ty) -> bool { apply(&|u| u == t) }");
        by_value("fn inner<G: Fn(Ty) -> bool>(g: G) -> bool { g(Ty::A) }\nfn outer<F: Fn(Ty) -> bool>(f: F) -> bool { inner(f) }\npub fn g(t: Ty) -> bool { outer(|u| u == t) }");
        // another crate's code running this crate's `next` under a generic bound
        by_value("pub struct W { i: u8 }\nimpl Iterator for W { type Item = Ty; fn next(&mut self) -> Option<Ty> { self.i += 1; if self.i > 2 { None } else { Some(Ty::A) } } }\nfn any_is<I: Iterator<Item = Ty>>(mut it: I, t: Ty) -> bool { it.any(|u| u == t) }\npub fn f(t: Ty) -> bool { any_is(W { i: 0 }, t) }");
        // a function pointer's result is what the function returns
        by_value("fn mk_key() -> Key { Key { kind: Ty::C, id: 0 } }\npub fn f(t: Ty) -> bool { let p: fn() -> Key = mk_key; p().kind == t }");
        // controls: a static function pointer is no fixed value; a function
        // called by its name is not taken as a value (verifier land-clean-r1
        // NOTE: `same(x, y)` fed its parameters from every pointer call)
        passes("fn id(t: Ty) -> Ty { t }\nstatic ID: fn(Ty) -> Ty = id;\npub fn f(t: Ty, u: Ty) -> bool { ID(u) == t }");
        passes("fn same(a: Ty, b: Ty) -> bool { a == b }\npub fn f(x: Ty, y: Ty) -> bool { same(x, y) }\nfn g(p: fn(Ty, Ty) -> bool) -> bool { p(Ty::A, Ty::C) }\nfn h(a: Ty, b: Ty) -> bool { let _ = (a, b); true }\npub fn k() -> bool { g(h) }");
    }

    #[test]
    fn a_discriminant_cast_is_refused() {
        // verifier r11v `discr_cast`: the projector's own `ops::cc` did this.
        refused(
            "pub enum Cc { C, Fast }\npub fn f(c: Cc) -> u32 { c as u32 }",
            "a discriminant cast",
        );
        refused(
            "pub enum Cc { C, Fast }\npub const TAG: u8 = Cc::Fast as u8;",
            CATCH_ALL,
        );
    }

    #[test]
    fn agreement_and_an_assertion_are_not_a_told_variant() {
        // two values, neither of them named: agreement, not a classification
        passes("pub fn f(a: &[Ty], b: &[Ty]) -> bool { a == b }");
        passes("pub fn f(a: Ty, ts: &[Ty]) -> bool { ts.contains(&a) }");
        passes("pub fn f(k: Key, t: Ty) -> bool { k.kind == t }");
        // a variant of an enum nobody gates
        passes("pub fn f(o: Option<Ty>) -> bool { o == None }");
        // a value that cannot hold a variant
        passes("pub fn f() -> bool { [Ty::A, Ty::C].len() == 2 }");
        // a function of this crate comparing what its callers computed
        passes("fn agree(a: &Ty, b: &Ty) -> bool { a == b }\npub fn f(x: Ty, y: Ty) -> bool { agree(&x, &y) }");
        // one call's variant does not reach another call's result or closure
        passes("fn id(t: Ty) -> Ty { t }\npub fn f(t: Ty, x: Ty) -> bool { let _ = id(Ty::A); id(x) == t }");
        passes("fn apply<F: Fn(Ty) -> bool>(f: F, v: Ty) -> bool { f(v) }\npub fn f(t: Ty) -> bool { apply(|_u| true, Ty::A) && apply(|u| u == t, t) }");
        // a trait method's call is the impl it resolves to, not every impl
        passes("pub trait P { fn p(&self, t: Ty) -> Ty; }\nimpl P for u8 { fn p(&self, t: Ty) -> Ty { t } }\nimpl P for u16 { fn p(&self, _t: Ty) -> Ty { Ty::A } }\npub fn f(t: Ty, u: Ty) -> bool { 1u8.p(u) == t }");
        // a variant of one enum is not in a value of a type that cannot hold
        // it, nor told apart by a comparison of another enum
        passes("#[derive(Clone, Copy, PartialEq)]\npub enum O { X, Y }\npub fn f(t: Ty, u: Ty, o: O) -> bool { let m = Some(Ty::A).map(|_| o); (m, t) == (m, u) }");
        passes("#[derive(Clone, Copy)]\npub enum O { X, Y }\nfn same_with<T: PartialEq>(a: T, b: T, _tag: O) -> bool { a == b }\npub fn f(x: Ty, y: Ty) -> bool { same_with(x, y, O::X) }");
        // a function of this crate that names no variant in its result
        passes("fn pass(t: Ty, n: u8) -> Ty { let _ = n; t }\npub fn f(t: Ty, x: Ty, n: u8) -> bool { pass(x, n) == t }");
        // the comparison `assert_eq!` / `assert_ne!` writes: its other outcome is a panic
        passes("pub fn f(t: Ty) { assert_eq!(t, Ty::A); assert_ne!(t, Ty::C); }");
        // ... and so is the comparison a builtin derive writes, which it calls
        passes("pub fn f(k: Key) { assert_eq!(k, EMPTY); }");
        // a bound that compares a type no gated enum is in
        passes("pub fn tag<T: PartialEq>(a: T, b: T, t: Ty) -> bool { let _ = t; a == b }\npub fn f() -> bool { tag(1u8, 2u8, Ty::A) }");
        // a builtin derive's comparisons and casts
        passes("#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]\npub enum O { X, Y(u8) }");
    }

    // ── which enums are gated ───────────────────────────────────────────────

    /// verifier r11v: with the gated crates emptied, every test above passed --
    /// each gates the fixture's own enum. This one compiles a crate named
    /// `trust_ir` and another named otherwise, and holds a dependent to both.
    #[test]
    fn trust_ir_s_enums_are_gated_and_no_other_crate_s() {
        let dir = scratch("gated-crates");
        let dep = "#![no_std]\n#[derive(Clone, Copy, PartialEq, Eq)]\npub enum K { A, B }\nimpl K { pub fn first() -> K { K::A } }\n";
        let gated = dependency(dep, "trust_ir", &dir);
        let other = dependency(dep, "other_ir", &dir);
        for (krate, rmeta, held) in [("trust_ir", &gated, true), ("other_ir", &other, false)] {
            let extern_arg = vec![
                "--extern".to_string(),
                format!("{krate}={}", rmeta.display()),
            ];
            for body in [
                "pub fn f(k: KRATE::K) -> u8 { match k { KRATE::K::A => 1, _ => 2 } }",
                "pub fn f(k: KRATE::K) -> bool { k == KRATE::K::A }",
                // a function of the other crate that reads no variable returns
                // one fixed variant: its body is not followed, its value is
                "pub fn f(k: KRATE::K) -> bool { k == KRATE::K::first() }",
            ] {
                let src = format!("#![no_std]\n{}\n", body.replace("KRATE", krate));
                let found = refusals_with(&src, "2021", "dependent", &extern_arg);
                assert_eq!(
                    found.iter().any(|f| f.contains(CATCH_ALL)),
                    held,
                    "{krate}: {body}\ngot {found:?}"
                );
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// P5 (verifier land-clean-r1): a fixed value of the gated crate was
    /// named only when its type was a gated enum -- `K::first()` was refused,
    /// an array of variants, a structure holding one and an `impl Iterator` of
    /// them passed.
    #[test]
    fn a_fixed_value_of_the_gated_crate_names_what_it_holds() {
        let dir = scratch("gated-fixed");
        let dep = "#![no_std]\n#[derive(Clone, Copy, PartialEq, Eq, Default)]\npub enum K { #[default] A, B }\n#[derive(Clone, Copy, PartialEq, Eq, Default)]\npub struct S { pub k: K, pub n: u8 }\nimpl K { pub fn all() -> [K; 2] { [K::A, K::B] } pub fn iter() -> impl Iterator<Item = K> { [K::A, K::B].into_iter() } pub fn pick(n: u8) -> K { if n == 0 { K::A } else { K::B } } }\nimpl S { pub fn plain() -> S { S { k: K::A, n: 0 } } }\n";
        let gated = dependency(dep, "trust_ir", &dir);
        let extern_arg = vec![
            "--extern".to_string(),
            format!("trust_ir={}", gated.display()),
        ];
        for (body, held) in [
            (
                "pub fn f(k: trust_ir::K) -> bool { trust_ir::K::all().contains(&k) }",
                true,
            ),
            (
                "pub fn f(s: trust_ir::S) -> bool { s == trust_ir::S::default() }",
                true,
            ),
            (
                "pub fn f(s: trust_ir::S) -> bool { s == trust_ir::S::plain() }",
                true,
            ),
            (
                "pub fn f(k: trust_ir::K) -> bool { trust_ir::K::iter().any(|j| j == k) }",
                true,
            ),
            // controls: two values the crate did not fix; a gated function's
            // result that reads a variable (agreement, out of model)
            (
                "pub fn f(s: trust_ir::S, t: trust_ir::S) -> bool { s == t }",
                false,
            ),
            (
                "pub fn f(k: trust_ir::K, n: u8) -> bool { k == trust_ir::K::pick(n) }",
                false,
            ),
        ] {
            let src = format!("#![no_std]\n{body}\n");
            let found = refusals_with(&src, "2021", "dependent", &extern_arg);
            assert_eq!(
                found.iter().any(|f| f.contains(BY_VALUE)),
                held,
                "{body}\ngot {found:?}"
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    // ── an incremental session ──────────────────────────────────────────────

    /// verifier r11v NOTE: every r11 run was CARGO_INCREMENTAL=0, and the hook
    /// compiles incrementally. A rerun loads the compilation's results from the
    /// session; the scan must read every body again, and refuse again.
    #[test]
    fn an_incremental_rerun_scans_every_body_again() {
        let dir = scratch("incremental");
        let session = vec!["-C".to_string(), format!("incremental={}", dir.display())];
        let clean = format!(
            "{TY}pub fn f(t: Ty) -> u8 {{ match t {{ Ty::A => 1, Ty::B(n) => n, Ty::C => 3 }} }}\n"
        );
        // a catch-all and a comparison: both rules, again on every rerun
        let planted = format!(
            "{TY}pub fn f(t: Ty) -> u8 {{ match t {{ Ty::A => 1, _ => 2 }} }}\npub fn g(t: Ty) -> u8 {{ if t == Ty::A {{ 1 }} else {{ 3 }} }}\n"
        );
        for (src, held) in [
            (&planted, true),
            (&planted, true),
            (&clean, false),
            (&planted, true),
        ] {
            let found = refusals_with(src, "2021", "fixture", &session);
            let rules = [
                found
                    .iter()
                    .any(|f| f.contains(CATCH_ALL) && !f.contains(BY_VALUE)),
                found.iter().any(|f| f.contains(BY_VALUE)),
            ];
            assert_eq!(rules, [held, held], "{src}\ngot {found:?}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
}

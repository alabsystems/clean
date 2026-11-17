// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KR0: the fenced Lean-reference entry.
//!
//! [`ReferenceKernel`] is the one door through which a check runs in Lean 4's
//! kernel theory and nothing else, and [`ReferenceAccepted`] is the token it
//! issues. The fence is the type: the token's fields are private and it is
//! built only in this module, so a caller that requires a `ReferenceAccepted`
//! knows the term went through every rule below. A row's theory is read off
//! the token ([`ReferenceAccepted::theory_id`]), never parsed from a string.
//!
//! # What the entry enforces
//!
//! * **One theory, one mode, fixed at construction.** [`ReferenceKernel::new`]
//!   sets [`KernelTheory::LeanReference`] (Lean's kernel exactly: the fourteen
//!   `Nat` literal extensions of `type_checker::reduce_nat` and no other native
//!   reducer) and [`CleanMode::Constructive`] (the mode `mode.rs` names as Lean
//!   4's core type theory) on the environment it takes by value. The
//!   environment never leaves as `&mut`, and the entry has no setter for
//!   either, so every `TypeChecker` built inside (`add_decl`,
//!   `check_decl_readonly_strict`) runs in both.
//! * **Every other checker setting is classified.** The type checkers built
//!   inside read the environment-wide flags through ONE snapshot,
//!   [`Environment::checker_settings`], and `new` destructures it with no rest
//!   pattern, so a new setting does not compile until it is classified here.
//!   Cumulative (Coq/pCIC) subtyping is not Lean's (`Sort 1 ≤ Sort 2` admits
//!   `def d : Sort 2 := Nat`, which Lean's kernel refuses), so a base that has
//!   it on, or EVER had it on (constants admitted then keep their stamps),
//!   refuses with [`ReferenceRefusal::NonLeanSetting`]. The heartbeat budget,
//!   the cache bound and the profiler can only turn an acceptance into a
//!   refusal, or nothing, and pass.
//! * **The base is checked, not trusted.** `new` walks every expression the
//!   base holds — constant types and values, inductive, constructor and
//!   recursor types, recursor rule right-hand sides — with ONE [`ExprKind`]
//!   match that has no wildcard arm, so a new expression form does not compile
//!   until someone classifies it here. Any of the fourteen non-Lean forms
//!   ([`NonLeanKind`]) refuses. So does any constant that did not pass the full
//!   kernel check: `add_decl_structural`, an unchecked insertion, a structural
//!   `.olean` import, a lazily served constant, or unknown provenance. There
//!   is no exception for inductive families: `add_inductive` stamps a
//!   family's head and constructors, and — after its mandatory authority gate
//!   (`validate_and_stamp_recursor`) — its generated eliminators,
//!   `FullKernelCheck`. The same provenance is required of every inductive,
//!   constructor, recursor and quotient primitive by name, and quotient
//!   primitive types are walked too.
//! * **The base is re-checked where it is used (KR1 increment 3, R143).** A
//!   `FullKernelCheck` stamp says the constant passed the kernel in the
//!   theory, mode and settings it was added under, not in this entry's (a
//!   base built under `Extended` or `Classical`, as `Environment::with_prelude`
//!   is, carries such stamps). So no base record counts as reference-checked
//!   on its stamp: the first check that cites one re-checks it, and every base
//!   record its closure reaches, in this entry's settings, dependencies first
//!   ([`ReferenceRefusal::BaseRecheck`] on a failure). Dependencies-first
//!   needs an acyclic closure, so a citation cycle through anything but an
//!   inductive family's own records (a self-citation included) refuses too:
//!   two base theorems proving `∀ p, p` from each other would otherwise each
//!   re-check with the other resident. What the re-check covers is listed
//!   on `recheck_one`; an inductive family's admission (positivity and
//!   universe checks included) is re-run by the kernel and every resident
//!   member compared with the generated one (R161). A base built through the entry
//!   (`clean_olean::reference_base_closed`, which starts EMPTY and admits
//!   every declaration through [`Self::add_checked`],
//!   [`Self::add_inductive_checked`] and [`Self::add_quot_checked`]) needs no
//!   re-check: nothing in it came from a base. The native-reducer and
//!   `implemented_by` tables are not walked: under
//!   [`KernelTheory::LeanReference`] the checker fires no registered reducer
//!   but Lean's own `Nat` extensions, and those are computed by
//!   `type_checker::reduce_nat`, not read from the table (a lying reducer
//!   registered under `Nat.add` does not make `2 + 2 = 5` check). The folds
//!   COMPILED INTO the checker that Lean's kernel lacks (`reduce_int` over a
//!   big literal, the `Nat.pred` arm of `reduce_nat`, the evaluation of
//!   `Lean.reduceBool`/`Lean.reduceNat` by whnf) take the same rule since
//!   self-proof unit F1 (`tc/fold_admission.rs`, `hardwired_fold_admitted`):
//!   they asked native-fold authority alone before it, and fired here.
//! * **Ax0 (KR1 increment 3, R143).** Every closure through the entry is ⊆
//!   Ax0 (`propext`, `Quot.sound`, `Classical.choice`) plus the quotient
//!   formers: a check whose closure reaches a base axiom that is neither a
//!   tripwire nor the kernel's canonical foundational constant of its name
//!   refuses with [`ReferenceRefusal::OutsideAx0`] (a base may HOLD one, as
//!   `with_prelude` holds the `IO` signatures), and `add_checked` admits an
//!   axiom only when it is such a canonical declaration. Canonical means the
//!   statement AND what it names: `propext`'s `Iff` and `Eq`,
//!   `Classical.choice`'s `Nonempty` and the quotient's `Eq` must be Lean's
//!   own inductives of exactly the shape the axiom assumes
//!   (`Environment::check_foundation_premises`); over a `def Nonempty :=
//!   fun _ => ∀ p : Prop, p → p` the canonical `Classical.choice` proves
//!   `∀ p : Prop, p`.
//! * **Tripwires (KR1 slice 1).** No closure through the entry may reach one
//!   of Lean `Init`'s declared but unreachable axioms ([`TRIPWIRE_AXIOMS`]:
//!   `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`,
//!   `Lean.trustCompiler`, the compiler's `lc*` constants) or one of Clean's
//!   own trust markers (`sorry`, `trustedArith`, `trustedAy`: each a
//!   `{α : Sort u} → α` axiom `with_prelude` declares, the list
//!   `crate::is_trust_marker` reads); [`is_tripwire`] is the test.
//!   A declaration, closed term or inductive block that names one, cites one,
//!   or cites a base constant whose closure reaches one refuses with
//!   [`ReferenceRefusal::Tripwire`]; so does declaring one through the entry.
//!   The base closure is computed once by `new`, over the edges Lean's
//!   `CollectAxioms` follows: a constant's type and value, a recursor's type
//!   and rules, and an inductive type to each of its constructors (so citing
//!   `T` reaches a tripwire one of `T`'s constructors cites). A base may HOLD
//!   a tripwire (Lean's `Init` and `with_prelude` both do): only reaching it
//!   refuses.
//! * **Only the checked path.** [`ReferenceKernel::add_checked`] refuses up
//!   front while a Metamath two-pass scope is live on the thread
//!   (`mm_two_pass_active`, or the bare axiom-only flag), then walks the
//!   declaration and every constant it cites, then calls `add_decl` — never
//!   `add_decl_structural`, never `add_decl_unchecked`. An inductive block
//!   goes through `add_inductive_core` (Lean's admission: the recursors and
//!   ι-rules are regenerated by the kernel), the quotient primitives through
//!   `add_quot` (after `Eq` was admitted through the entry), each with the
//!   same up-front refusals and walks. Generated members (recursors,
//!   quotient primitives) join the checked set only after their provenance
//!   and forms are checked post-admission.
//!
//! # Refusals
//!
//! A kernel refusal is reported as [`ReferenceRefusal::TheoryExclusion`] when
//! the kernel's own type mismatch (`TypeCheckFailed`) comes from a term whose
//! δ-closure reaches a registered native reducer that Lean's profile excludes
//! (`Environment::lean_theory_exclusion`): Clean's extended theory would have
//! computed that head, Lean's kernel cannot. Every other kernel refusal is
//! [`ReferenceRefusal::Kernel`]. The classification only names the refusal;
//! it never turns one into an acceptance.
//!
//! # Identities
//!
//! [`TheoryId`] names the reduction theory and nothing else: its digest is
//! computed from the fourteen `LEAN_KERNEL_NAT_EXTENSIONS` heads plus the
//! `string-literal-expansion` tag, and names no Lean version. The environment
//! is identified separately by [`EnvDigest`]: the content digest of the base
//! at construction, chained with the digest of every declaration admitted
//! through the entry since. KR1 fences the environment; this module only
//! names it.
//!
//! # The fence, as compile-time facts
//!
//! The entry has no way to change its theory or mode, and no `&mut` access to
//! its environment:
//!
//! ```compile_fail
//! fn f(k: &mut clean_kernel::ReferenceKernel) {
//!     k.set_kernel_theory(clean_kernel::env::KernelTheory::Extended);
//! }
//! ```
//!
//! ```compile_fail
//! fn f(k: &mut clean_kernel::ReferenceKernel) {
//!     k.set_mode(clean_kernel::CleanMode::Classical);
//! }
//! ```
//!
//! ```compile_fail
//! fn f(k: &mut clean_kernel::ReferenceKernel) {
//!     let _ = k.env_mut();
//! }
//! ```
//!
//! ```compile_fail
//! fn f(k: &mut clean_kernel::ReferenceKernel) {
//!     k.environment().set_kernel_theory(clean_kernel::env::KernelTheory::Extended);
//! }
//! ```
//!
//! and a token cannot be built outside this module:
//!
//! ```compile_fail
//! fn f(t: clean_kernel::TheoryId, e: clean_kernel::EnvDigest) -> clean_kernel::ReferenceAccepted {
//!     clean_kernel::ReferenceAccepted { theory_id: t, env_digest: e, decl_digest: [0; 32] }
//! }
//! ```
//!
//! The positive control for the five blocks above: the same items, used
//! through the API the entry does expose, compile.
//!
//! ```
//! fn f(k: &mut clean_kernel::ReferenceKernel, d: clean_kernel::Declaration)
//!     -> Result<clean_kernel::ReferenceAccepted, clean_kernel::ReferenceRefusal>
//! {
//!     let _: clean_kernel::TheoryId = k.theory_id();
//!     let _: clean_kernel::EnvDigest = k.env_digest();
//!     let _: &clean_kernel::Environment = k.environment();
//!     k.add_checked(d)
//! }
//! ```

use std::collections::HashSet;

use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::env::{
    closed_term_content_digest, declaration_content_digest, inductive_content_digest,
    is_canonical_foundational_constant, mm_axiom_only, mm_two_pass_active, quotient_content_digest,
    CheckerSettings, ConstantInfo, ConstantKind, Declaration, DeclarationVerification, EnvError,
    Environment, KernelTheory, LeanTheoryExclusion, Reducibility, LEAN_KERNEL_NAT_EXTENSIONS,
};
use crate::expr::{Expr, ExprKind, UsedConstants};
use crate::inductive::InductiveDecl;
use crate::mode::CleanMode;
use crate::name::{Name, NameInner};

/// The tag that, with the `Nat` heads, makes up the reference theory: Lean's
/// kernel expands a string literal to `String.ofList` of `Char.ofNat`s
/// (`string_lit_to_constructor`).
pub const STRING_LITERAL_EXPANSION_TAG: &str = "string-literal-expansion";

/// Domain separator of [`theory_digest`].
const THEORY_DIGEST_DOMAIN: &str = "clean.reference-kernel.theory-id.v1";

/// [`theory_digest`] of `LEAN_KERNEL_NAT_EXTENSIONS` plus
/// [`STRING_LITERAL_EXPANSION_TAG`], pinned. A unit test recomputes it from the
/// live list, so changing the `Nat` set or the string tag without bumping
/// [`TheoryId`] fails.
const LEAN_REFERENCE_V1_DIGEST: [u8; 32] = [
    0x3a, 0x3b, 0x95, 0xbe, 0x37, 0x20, 0x96, 0xca, 0x4b, 0xac, 0x5c, 0xbc, 0xb3, 0x5f, 0x78, 0x97,
    0x75, 0x40, 0x8f, 0x94, 0xc1, 0x96, 0x70, 0x25, 0x7a, 0x57, 0x18, 0x8d, 0x71, 0xb5, 0x35, 0x91,
];

/// Domain separators of the environment digest chain.
const ENV_BASE_DOMAIN: &str = "clean.reference-kernel.env-base.v1";
const ENV_STEP_DOMAIN: &str = "clean.reference-kernel.env-step.v1";

/// The name `check_closed_term` checks its pair under. Read-only: nothing is
/// added to the environment under it.
const CLOSED_TERM_NAME: &str = "_clean_reference.closed_term";

/// Most constants the refusal classifier visits on one δ-closure walk before
/// it stops (the refusal then stays [`ReferenceRefusal::Kernel`]).
const CLASSIFY_CLOSURE_CAP: usize = 100_000;

/// Lean `Init`'s declared but unreachable axioms (KR1, proven-core plan): the
/// elaborator's `sorry`, the two `native_decide` bridges, the compiler-trust
/// marker, and the compiler's `lc*` constants as v4.30.0-rc2 declares them
/// (`Init/Prelude.lean`, `Init/Core.lean`). No closure through the entry may
/// reach one ([`ReferenceRefusal::Tripwire`]). [`is_tripwire`] also catches
/// any other root-level `lc` + uppercase name, so a new compiler constant is
/// refused before it is listed.
pub const TRIPWIRE_AXIOMS: [&str; 10] = [
    "sorryAx",
    "Lean.ofReduceBool",
    "Lean.ofReduceNat",
    "Lean.trustCompiler",
    "lcErased",
    "lcAny",
    "lcVoid",
    "lcProof",
    "lcCast",
    "lcUnreachable",
];

/// Whether `name` is a tripwire: one of [`TRIPWIRE_AXIOMS`]; one of Clean's
/// trust markers (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`,
/// `crate::is_trust_marker`: each lets any type be inhabited, so a closure
/// through one proves `False`); or a root-level (one-component) name spelled
/// `lc` followed by an ASCII uppercase letter — the compiler's naming of its
/// erased-term constants. A root `lcm` is not one; `Nat.lcm` is not
/// root-level.
#[must_use]
pub fn is_tripwire(name: &Name) -> bool {
    if crate::env::is_trust_marker(name) {
        return true;
    }
    if let NameInner::Str(parent, s) = name.inner() {
        if matches!(parent.inner(), NameInner::Anon) {
            let mut rest = s.strip_prefix("lc").unwrap_or("").chars();
            if rest.next().is_some_and(|c| c.is_ascii_uppercase()) {
                return true;
            }
        }
    }
    let rendered = name.to_string();
    TRIPWIRE_AXIOMS.contains(&rendered.as_str())
}

/// The reduction theory a [`ReferenceAccepted`] was issued in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TheoryId {
    /// Lean 4's kernel theory: the `Nat` literal extensions of
    /// `type_checker::reduce_nat` (`LEAN_KERNEL_NAT_EXTENSIONS`) and the
    /// string-literal expansion, over [`CleanMode::Constructive`]. Names no
    /// Lean version; the environment is the [`EnvDigest`].
    LeanReferenceV1,
}

impl TheoryId {
    /// The pinned digest of this theory's inputs ([`theory_digest`] of
    /// [`Self::nat_extensions`] and [`Self::tags`]).
    #[must_use]
    pub fn digest(self) -> [u8; 32] {
        match self {
            Self::LeanReferenceV1 => LEAN_REFERENCE_V1_DIGEST,
        }
    }

    /// The `Nat` heads this theory computes natively on literals.
    #[must_use]
    pub fn nat_extensions(self) -> &'static [&'static str] {
        match self {
            Self::LeanReferenceV1 => &LEAN_KERNEL_NAT_EXTENSIONS,
        }
    }

    /// The non-`Nat` kernel extensions this theory has, as tags.
    #[must_use]
    pub fn tags(self) -> &'static [&'static str] {
        match self {
            Self::LeanReferenceV1 => &[STRING_LITERAL_EXPANSION_TAG],
        }
    }

    /// The kernel theory every check of this id runs in.
    #[must_use]
    pub fn kernel_theory(self) -> KernelTheory {
        match self {
            Self::LeanReferenceV1 => KernelTheory::LeanReference,
        }
    }

    /// The mode every check of this id runs in.
    #[must_use]
    pub fn mode(self) -> CleanMode {
        match self {
            Self::LeanReferenceV1 => CleanMode::Constructive,
        }
    }
}

/// SHA-256 over a theory's inputs: the domain, then each `Nat` head and each
/// tag, every field length-prefixed so adjacent fields never run together.
#[must_use]
pub fn theory_digest(nat_extensions: &[&str], tags: &[&str]) -> [u8; 32] {
    let mut h = Sha256::new();
    put(&mut h, THEORY_DIGEST_DOMAIN.as_bytes());
    h.update((nat_extensions.len() as u64).to_le_bytes());
    for head in nat_extensions {
        put(&mut h, head.as_bytes());
    }
    h.update((tags.len() as u64).to_le_bytes());
    for tag in tags {
        put(&mut h, tag.as_bytes());
    }
    h.finalize().into()
}

fn put(h: &mut Sha256, bytes: &[u8]) {
    h.update((bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

/// The environment a [`ReferenceAccepted`] was issued against: the content
/// digest of the entry's base, chained with every declaration admitted
/// through the entry since (see the module docs).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EnvDigest(pub [u8; 32]);

/// The fourteen expression forms Clean has and Lean 4's kernel does not.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NonLeanKind {
    /// `ExprKind::SProp`.
    SProp,
    /// `ExprKind::Squash`.
    Squash,
    /// `ExprKind::CubicalInterval`.
    CubicalInterval,
    /// `ExprKind::CubicalI0`.
    CubicalI0,
    /// `ExprKind::CubicalI1`.
    CubicalI1,
    /// `ExprKind::CubicalPath`.
    CubicalPath,
    /// `ExprKind::CubicalPathLam`.
    CubicalPathLam,
    /// `ExprKind::CubicalPathApp`.
    CubicalPathApp,
    /// `ExprKind::CubicalHComp`.
    CubicalHComp,
    /// `ExprKind::CubicalTransp`.
    CubicalTransp,
    /// `ExprKind::CubicalCoe`.
    CubicalCoe,
    /// `ExprKind::ZFCSet`.
    ZFCSet,
    /// `ExprKind::ZFCMem`.
    ZFCMem,
    /// `ExprKind::ZFCComprehension`.
    ZFCComprehension,
}

/// Why the reference entry refused.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReferenceRefusal {
    /// `decl` — the declaration itself, or a constant it cites — contains an
    /// expression form Lean's kernel does not have.
    #[error("`{decl}` contains the non-Lean expression form {kind:?}")]
    NonLeanExprKind {
        /// The declaration or cited constant that holds the form.
        decl: Name,
        /// The form.
        kind: NonLeanKind,
    },
    /// The kernel refused, and the term's δ-closure reaches a native reducer
    /// Lean's kernel does not have, for this reason.
    #[error("refused in Lean's reference theory; the term relies on a reducer Lean's kernel lacks: {0:?}")]
    TheoryExclusion(LeanTheoryExclusion),
    /// `decl` is in the environment without having passed the full kernel
    /// check (structural, unchecked, imported, lazily served, or unknown).
    #[error("`{decl}` entered the environment without a full kernel check")]
    StructuralProvenance {
        /// The constant.
        decl: Name,
    },
    /// A Metamath two-pass scope (or its axiom-only flag) is live on this
    /// thread, so `add_decl` could drop a proof.
    #[error("a Metamath two-pass scope is active on this thread")]
    MmTwoPassActive,
    /// The base has a checker setting Lean's kernel does not have (see
    /// [`Environment::checker_settings`]).
    #[error("the base has the non-Lean checker setting `{setting}`")]
    NonLeanSetting {
        /// The setting.
        setting: &'static str,
    },
    /// `decl`'s closure — the declaration itself, a constant it cites, or a
    /// base constant such a citation reaches — contains the tripwire
    /// `reached` ([`TRIPWIRE_AXIOMS`], [`is_tripwire`]).
    #[error("`{decl}` reaches the tripwire `{reached}`, which no reference closure may contain")]
    Tripwire {
        /// The declaration being checked.
        decl: Name,
        /// The tripwire constant its closure reaches.
        reached: Name,
    },
    /// `decl`'s closure reaches the axiom `reached`, which is not in Ax0
    /// (`propext`, `Quot.sound`, `Classical.choice` at their canonical
    /// statements) and not a quotient former (`Quot`, `Quot.mk`, `Quot.lift`,
    /// `Quot.ind`): KR1 increment 3 (`docs/DECISIONS.md` R143). Also returned
    /// for declaring such an axiom through the entry.
    #[error(
        "`{decl}` reaches the axiom `{reached}`, which is outside Ax0 and the quotient formers"
    )]
    OutsideAx0 {
        /// The declaration being checked.
        decl: Name,
        /// The axiom its closure reaches.
        reached: Name,
    },
    /// A constant `new`'s base handed in did not pass its re-check through
    /// the entry (R143): its stamp was earned under whatever theory, mode and
    /// settings the base was built in, so the entry re-checks it, in Lean's,
    /// the first time a check cites it.
    #[error("base constant `{decl}` fails its re-check in Lean's reference theory: {reason}")]
    BaseRecheck {
        /// The base constant.
        decl: Name,
        /// The kernel's reason.
        reason: String,
    },
    /// The quotient primitives were asked for twice, or after the base already
    /// held them, or an inductive family through the entry was empty.
    #[error("{0}")]
    Admission(String),
    /// The kernel's own refusal.
    #[error(transparent)]
    Kernel(EnvError),
}

/// The token the entry issues for an accepted check. Its fields are private
/// and it is constructed only in this module; it is deliberately neither
/// `Clone` nor `Deserialize`.
#[derive(Debug, PartialEq, Eq)]
pub struct ReferenceAccepted {
    theory_id: TheoryId,
    env_digest: EnvDigest,
    decl_digest: [u8; 32],
}

impl ReferenceAccepted {
    /// The theory the check ran in.
    #[must_use]
    pub fn theory_id(&self) -> TheoryId {
        self.theory_id
    }

    /// The environment the check ran against (for `add_checked`, the
    /// environment AFTER the declaration was admitted).
    #[must_use]
    pub fn env_digest(&self) -> EnvDigest {
        self.env_digest
    }

    /// The content digest of what was checked: the declaration, or the closed
    /// `(type, value)` pair.
    #[must_use]
    pub fn decl_digest(&self) -> [u8; 32] {
        self.decl_digest
    }
}

/// The fenced Lean-reference entry (see the module docs).
#[derive(Debug)]
pub struct ReferenceKernel {
    env: Environment,
    theory_id: TheoryId,
    env_digest: EnvDigest,
    /// Constants whose expressions and provenance this entry has checked.
    walked: HashSet<Name>,
    /// The subset of `walked` admitted through the entry's own methods (not
    /// handed in by `new`'s base).
    admitted: HashSet<Name>,
    /// Base constants whose closure reaches a tripwire, each with the
    /// tripwire it reaches (computed once by `new`; nothing admitted through
    /// the entry is ever added, because admission refuses it).
    tainted: std::collections::HashMap<Name, Name>,
    /// Base constants whose closure reaches an axiom outside Ax0 and the
    /// quotient formers, each with one such axiom (computed once by `new`,
    /// over the same edges as `tainted`; admission refuses any such axiom,
    /// so nothing admitted is ever added).
    outside_ax0: std::collections::HashMap<Name, Name>,
    /// Every name `new`'s base held: present, walked, and NOT yet re-checked
    /// in this entry's theory (R143).
    base: HashSet<Name>,
    /// The subset of `base` re-checked through the entry so far (a citation
    /// re-checks the cited base constant's whole closure, once).
    rechecked: std::sync::Mutex<HashSet<Name>>,
    /// The base inductive blocks (by first type) whose admission the
    /// re-check has re-run through the kernel (R161), once per block, each
    /// with the members the kernel generated for it.
    replayed_blocks:
        std::sync::Mutex<std::collections::HashMap<Name, std::collections::BTreeSet<Name>>>,
}

impl ReferenceKernel {
    /// Take `base`, check every expression and the provenance of every
    /// constant it holds, and fix its theory and mode.
    ///
    /// # Errors
    ///
    /// [`ReferenceRefusal::NonLeanSetting`] for a checker setting Lean's
    /// kernel does not have, [`ReferenceRefusal::NonLeanExprKind`] for a
    /// non-Lean expression form anywhere in the base,
    /// [`ReferenceRefusal::StructuralProvenance`] for a constant that did not
    /// pass the full kernel check. When several constants would refuse, the
    /// one whose name sorts first is reported.
    pub fn new(base: Environment) -> Result<Self, ReferenceRefusal> {
        let theory_id = TheoryId::LeanReferenceV1;
        check_settings(&base)?;
        let mut lazy = base.lazy_source_names();
        lazy.sort_by_cached_key(Name::to_string);
        if let Some(decl) = lazy.into_iter().next() {
            return Err(ReferenceRefusal::StructuralProvenance { decl });
        }

        let mut names: Vec<&Name> = base.constants().map(|c| &c.name).collect();
        names.sort_by_cached_key(|n| n.to_string());
        // The kernel's other records, by name: each one's provenance too.
        let mut records: Vec<&Name> = base
            .inductives()
            .map(|i| &i.name)
            .chain(base.constructors().map(|c| &c.name))
            .chain(base.recursors().map(|r| &r.name))
            .chain(base.quotients().map(|q| &q.name))
            .collect();
        records.sort_by_cached_key(|n| n.to_string());
        for name in names.iter().chain(records.iter()) {
            if !provenance_full(&base, name) {
                return Err(ReferenceRefusal::StructuralProvenance {
                    decl: (*name).clone(),
                });
            }
        }

        // Every expression the base holds, keyed by the record that holds it.
        let mut roots: Vec<(&Name, &Expr)> = Vec::new();
        // Values before types, so a form that only TYPES another (`Squash A :
        // SProp`) does not hide the form the value is written in.
        for c in base.constants() {
            if let Some(v) = &c.value {
                roots.push((&c.name, v));
            }
            roots.push((&c.name, &c.type_));
        }
        for i in base.inductives() {
            roots.push((&i.name, &i.type_));
        }
        for c in base.constructors() {
            roots.push((&c.name, &c.type_));
        }
        for r in base.recursors() {
            roots.push((&r.name, &r.type_));
            for rule in &r.rules {
                roots.push((&r.name, &rule.rhs));
            }
        }
        for q in base.quotients() {
            roots.push((&q.name, &q.type_));
        }
        roots.sort_by_cached_key(|(n, _)| n.to_string());
        let mut walk = KindWalk::default();
        for (name, e) in roots {
            if let Some(kind) = walk.first_non_lean(e) {
                return Err(ReferenceRefusal::NonLeanExprKind {
                    decl: name.clone(),
                    kind,
                });
            }
        }
        let walked: HashSet<Name> = names.into_iter().cloned().collect();
        let mut base_names: HashSet<Name> = walked.clone();
        base_names.extend(records.into_iter().cloned());
        let graph = CitationGraph::of(&base);
        let tainted = graph.taint(graph.tripwire_seeds.clone());
        let outside_ax0 = graph.taint(outside_ax0_axioms(&base));

        let content = base.content_digest();
        let mut env = base;
        env.set_kernel_theory(theory_id.kernel_theory());
        env.force_mode_for_reference_entry(theory_id.mode());
        let forced = env.checker_settings();
        if forced.kernel_theory != theory_id.kernel_theory() || forced.mode != theory_id.mode() {
            return Err(ReferenceRefusal::NonLeanSetting {
                setting: "kernel theory or mode not forced",
            });
        }

        let mut h = Sha256::new();
        put(&mut h, ENV_BASE_DOMAIN.as_bytes());
        put(&mut h, &theory_id.digest());
        put(&mut h, &[theory_id.mode() as u8]);
        put(&mut h, content.total.as_bytes());
        let env_digest = EnvDigest(h.finalize().into());

        Ok(Self {
            env,
            theory_id,
            env_digest,
            walked,
            admitted: HashSet::new(),
            tainted,
            outside_ax0,
            base: base_names,
            rechecked: std::sync::Mutex::new(HashSet::new()),
            replayed_blocks: std::sync::Mutex::new(std::collections::HashMap::new()),
        })
    }

    /// Check `d` in Lean's reference theory and, on success, add it.
    ///
    /// # Errors
    ///
    /// [`ReferenceRefusal::MmTwoPassActive`] while a Metamath two-pass scope
    /// is live; [`ReferenceRefusal::NonLeanExprKind`] when `d` or a constant
    /// it cites holds a non-Lean form; [`ReferenceRefusal::StructuralProvenance`]
    /// when a cited constant did not pass the full kernel check;
    /// [`ReferenceRefusal::TheoryExclusion`] or [`ReferenceRefusal::Kernel`]
    /// when the kernel refuses. Nothing is added on any refusal.
    pub fn add_checked(&mut self, d: Declaration) -> Result<ReferenceAccepted, ReferenceRefusal> {
        self.add_checked_inner(d, None)
    }

    /// Check a definition through the same fenced entry and preserve its exact
    /// ordinary reducibility hint. Both the declaration and the explicit hint
    /// are bound into the returned token and environment chain. No mutable
    /// environment is exposed, and all ordinary entry refusals remain in force.
    pub fn add_checked_with_reducibility(
        &mut self,
        d: Declaration,
        hint: Reducibility,
    ) -> Result<ReferenceAccepted, ReferenceRefusal> {
        self.add_checked_inner(d, Some(hint))
    }

    fn add_checked_inner(
        &mut self,
        d: Declaration,
        hint: Option<Reducibility>,
    ) -> Result<ReferenceAccepted, ReferenceRefusal> {
        if mm_two_pass_active() || mm_axiom_only() {
            return Err(ReferenceRefusal::MmTwoPassActive);
        }
        let (name, type_, value) = decl_parts(&d);
        let name = name.clone();
        if is_tripwire(&name) {
            return Err(ReferenceRefusal::Tripwire {
                reached: name.clone(),
                decl: name,
            });
        }
        // Value first (see `new`).
        let exprs: Vec<Expr> = value
            .cloned()
            .into_iter()
            .chain(std::iter::once(type_.clone()))
            .collect();
        self.check_terms(&name, &exprs)?;
        // Ax0 (R143), after the form walk (a non-Lean form is the more
        // specific refusal): the only axioms the entry admits are Lean's
        // three, at their canonical statements. Anything else would let a later
        // closure rest on an assumption Lean's `Init` does not make.
        if let Declaration::Axiom {
            level_params,
            type_,
            ..
        } = &d
        {
            let mut info = ConstantInfo::new(
                name.clone(),
                level_params.clone(),
                type_.clone(),
                None,
                false,
            );
            info.kind = ConstantKind::Axiom;
            // The statement's premises (`Iff`, `Eq`, `Nonempty`) are named,
            // not pinned, by the canonical comparison: each must be Lean's
            // own inductive here, or the canonical statement says something
            // else (R143).
            if !is_canonical_foundational_constant(&info)
                || self.env.check_foundation_premises(&name).is_err()
            {
                return Err(ReferenceRefusal::OutsideAx0 {
                    reached: name.clone(),
                    decl: name,
                });
            }
        }
        let mut decl_digest = declaration_content_digest(&d);
        if let Some(hint) = hint {
            let mut h = Sha256::new();
            put(&mut h, b"clean.reference.decl.reducibility.v1");
            put(&mut h, &decl_digest);
            let (tag, height) = match hint {
                Reducibility::Reducible => (0u8, 0u32),
                Reducibility::Regular(height) => (1, height),
                Reducibility::Irreducible => (2, 0),
                Reducibility::Opaque => (3, 0),
            };
            put(&mut h, &[tag]);
            put(&mut h, &height.to_le_bytes());
            decl_digest = h.finalize().into();
        }
        match hint {
            Some(hint) => self.env.add_decl_with_reducibility(d, hint),
            None => self.env.add_decl(d),
        }
        .map_err(|e| self.classify(e, &exprs))?;
        if !provenance_full(&self.env, &name) {
            // `add_decl` records `FullKernelCheck` on every success outside
            // the two-pass refused above; anything else is not a reference
            // acceptance, and the name stays out of `walked`, so a later
            // citation of it refuses too.
            return Err(ReferenceRefusal::StructuralProvenance { decl: name });
        }
        self.walked.insert(name.clone());
        self.admitted.insert(name);
        self.chain(&decl_digest);
        Ok(self.token(decl_digest))
    }

    /// Check the inductive family block `decl` in Lean's reference theory
    /// and, on success, add it: the family is re-validated by the kernel's
    /// Lean-faithful admission (`add_inductive_core`: positivity,
    /// constructor shape, universe constraints) and its recursors and ι-rules
    /// are regenerated by the kernel, never taken from the caller.
    ///
    /// # Errors
    ///
    /// As [`Self::add_checked`]; [`ReferenceRefusal::Admission`] for a block
    /// with no type. Nothing is added on a refusal before the kernel runs; a
    /// generated member that fails the post-admission provenance or form
    /// check stays out of the checked set, so citing it refuses.
    pub fn add_inductive_checked(
        &mut self,
        decl: InductiveDecl,
    ) -> Result<ReferenceAccepted, ReferenceRefusal> {
        if mm_two_pass_active() || mm_axiom_only() {
            return Err(ReferenceRefusal::MmTwoPassActive);
        }
        let Some(head) = decl.types.first().map(|t| t.name.clone()) else {
            return Err(ReferenceRefusal::Admission(
                "an inductive block with no type".to_string(),
            ));
        };
        let mut members: Vec<Name> = Vec::new();
        let mut exprs: Vec<Expr> = Vec::new();
        for ty in &decl.types {
            members.push(ty.name.clone());
            exprs.push(ty.type_.clone());
            for ctor in &ty.constructors {
                members.push(ctor.name.clone());
                exprs.push(ctor.type_.clone());
            }
        }
        if let Some(bad) = members.iter().find(|m| is_tripwire(m)) {
            return Err(ReferenceRefusal::Tripwire {
                decl: head,
                reached: bad.clone(),
            });
        }
        self.check_terms(&head, &exprs)?;
        let decl_digest = inductive_content_digest(&decl);
        let families: HashSet<Name> = decl.types.iter().map(|t| t.name.clone()).collect();
        self.env
            .add_inductive_core(decl)
            .map_err(|e| self.classify(e, &exprs))?;
        let mut generated: Vec<Name> = self
            .env
            .recursors()
            .filter(|r| families.contains(&r.inductive_name) && !self.walked.contains(&r.name))
            .map(|r| r.name.clone())
            .collect();
        generated.sort_by_cached_key(Name::to_string);
        members.extend(generated);
        self.admit_generated(&members)?;
        self.chain(&decl_digest);
        Ok(self.token(decl_digest))
    }

    /// Install the kernel's quotient primitives (`Quot`, `Quot.mk`,
    /// `Quot.lift`, `Quot.ind`, `Quot.sound`) through Lean's `add_quot`: the
    /// `Eq` their types name must already be in the entry, admitted through
    /// it ([`Self::add_inductive_checked`]; an `Eq` that came in `new`'s base
    /// does not count), with exactly the shape they assume.
    ///
    /// # Errors
    ///
    /// [`ReferenceRefusal::Admission`] when the primitives are already present
    /// (the kernel's `add_quot` would answer `Ok` again), or `Eq` was not
    /// admitted through the entry, or has the wrong shape;
    /// [`ReferenceRefusal::MmTwoPassActive`] as [`Self::add_checked`].
    pub fn add_quot_checked(&mut self) -> Result<ReferenceAccepted, ReferenceRefusal> {
        if mm_two_pass_active() || mm_axiom_only() {
            return Err(ReferenceRefusal::MmTwoPassActive);
        }
        if self.env.quot_installed() {
            return Err(ReferenceRefusal::Admission(
                "the quotient primitives are already installed".to_string(),
            ));
        }
        let eq = Name::from_string("Eq");
        if !self.admitted.contains(&eq) {
            return Err(ReferenceRefusal::Admission(
                "the quotient primitives need `Eq` admitted through the entry first".to_string(),
            ));
        }
        self.env.add_quot().map_err(ReferenceRefusal::Admission)?;
        let mut prims: Vec<(Name, Vec<Name>, Expr)> = self
            .env
            .quotients()
            .map(|q| (q.name.clone(), q.level_params.clone(), q.type_.clone()))
            .collect();
        prims.sort_by_cached_key(|(n, _, _)| n.to_string());
        let names: Vec<Name> = prims.iter().map(|(n, _, _)| n.clone()).collect();
        self.admit_generated(&names)?;
        let view: Vec<(&Name, &[Name], &Expr)> =
            prims.iter().map(|(n, l, t)| (n, l.as_slice(), t)).collect();
        let decl_digest = quotient_content_digest(&view);
        self.chain(&decl_digest);
        Ok(self.token(decl_digest))
    }

    /// After a kernel admission that generated `names`: each must carry the
    /// full-check stamp and hold no non-Lean form; then they join the checked
    /// set.
    fn admit_generated(&mut self, names: &[Name]) -> Result<(), ReferenceRefusal> {
        for name in names {
            if !provenance_full(&self.env, name) {
                return Err(ReferenceRefusal::StructuralProvenance { decl: name.clone() });
            }
            let mut walk = KindWalk::default();
            let mut roots: Vec<&Expr> = Vec::new();
            if let Some(info) = self.env.get_const(name) {
                roots.push(&info.type_);
                roots.extend(info.value.iter());
            }
            if let Some(r) = self.env.get_recursor(name) {
                roots.push(&r.type_);
                roots.extend(r.rules.iter().map(|rule| &rule.rhs));
            }
            if let Some(q) = self.env.get_quot(name) {
                roots.push(&q.type_);
            }
            for e in roots {
                if let Some(kind) = walk.first_non_lean(e) {
                    return Err(ReferenceRefusal::NonLeanExprKind {
                        decl: name.clone(),
                        kind,
                    });
                }
            }
        }
        self.walked.extend(names.iter().cloned());
        self.admitted.extend(names.iter().cloned());
        Ok(())
    }

    /// Chain `decl_digest` onto the environment digest.
    fn chain(&mut self, decl_digest: &[u8; 32]) {
        let mut h = Sha256::new();
        put(&mut h, ENV_STEP_DOMAIN.as_bytes());
        put(&mut h, &self.env_digest.0);
        put(&mut h, decl_digest);
        self.env_digest = EnvDigest(h.finalize().into());
    }

    /// Check that the closed term `val` has type `ty` in Lean's reference
    /// theory, without adding anything.
    ///
    /// # Errors
    ///
    /// As [`Self::add_checked`], less the two-pass refusal (nothing is
    /// added, so no proof can be dropped).
    pub fn check_closed_term(
        &self,
        ty: &Expr,
        val: &Expr,
    ) -> Result<ReferenceAccepted, ReferenceRefusal> {
        let name = Name::from_string(CLOSED_TERM_NAME);
        let exprs = [val.clone(), ty.clone()];
        self.check_terms(&name, &exprs)?;
        let decl = Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty.clone(),
            value: val.clone(),
            is_reducible: false,
        };
        self.env
            .check_decl_readonly_strict(&decl)
            .map_err(|e| self.classify(e, &exprs))?;
        Ok(self.token(closed_term_content_digest(ty, val)))
    }

    /// The theory every check of this entry runs in.
    #[must_use]
    pub fn theory_id(&self) -> TheoryId {
        self.theory_id
    }

    /// The environment the next check runs against.
    #[must_use]
    pub fn env_digest(&self) -> EnvDigest {
        self.env_digest
    }

    /// Read-only view of the environment (for inspection; nothing checked
    /// through it yields a [`ReferenceAccepted`]).
    #[must_use]
    pub fn environment(&self) -> &Environment {
        &self.env
    }

    fn token(&self, decl_digest: [u8; 32]) -> ReferenceAccepted {
        ReferenceAccepted {
            theory_id: self.theory_id,
            env_digest: self.env_digest,
            decl_digest,
        }
    }

    /// The pre-kernel walk: no non-Lean form in `exprs`, and every constant
    /// they cite is one this entry has checked (walked now if it was not).
    fn check_terms(&self, decl: &Name, exprs: &[Expr]) -> Result<(), ReferenceRefusal> {
        let mut walk = KindWalk::default();
        for e in exprs {
            if let Some(kind) = walk.first_non_lean(e) {
                return Err(ReferenceRefusal::NonLeanExprKind {
                    decl: decl.clone(),
                    kind,
                });
            }
        }
        let mut cited: HashSet<Name> = HashSet::new();
        for e in exprs {
            e.used_constants_dag(UsedConstants::WithProjectionStructures, &mut cited);
        }
        let mut cited: Vec<Name> = cited.into_iter().collect();
        cited.sort_by_cached_key(Name::to_string);
        for c in cited {
            if is_tripwire(&c) {
                return Err(ReferenceRefusal::Tripwire {
                    decl: decl.clone(),
                    reached: c,
                });
            }
            if let Some(reached) = self.tainted.get(&c) {
                return Err(ReferenceRefusal::Tripwire {
                    decl: decl.clone(),
                    reached: reached.clone(),
                });
            }
            if let Some(reached) = self.outside_ax0.get(&c) {
                return Err(ReferenceRefusal::OutsideAx0 {
                    decl: decl.clone(),
                    reached: reached.clone(),
                });
            }
            if self.base.contains(&c) && !self.admitted.contains(&c) {
                self.recheck_base_closure(&c)?;
                continue;
            }
            if self.walked.contains(&c) {
                continue;
            }
            // Not a constant this entry has checked. Absent names are the
            // kernel's to refuse; a present one is checked here, in full.
            let Some(info) = self.env.get_const(&c) else {
                continue;
            };
            if !provenance_full(&self.env, &c) {
                return Err(ReferenceRefusal::StructuralProvenance { decl: c });
            }
            let mut walk = KindWalk::default();
            for e in info.value.iter().chain(std::iter::once(&info.type_)) {
                if let Some(kind) = walk.first_non_lean(e) {
                    return Err(ReferenceRefusal::NonLeanExprKind { decl: c, kind });
                }
            }
        }
        Ok(())
    }

    /// Re-check `root`, a constant `new`'s base handed in, and every base
    /// constant its closure reaches, in this entry's theory, mode and
    /// settings (R143). Dependencies first (Lean's order), each once; the
    /// edges are those of the taint closure (`CitationGraph`).
    ///
    /// Dependencies-first needs the closure to be acyclic: a record checked
    /// while a record it cites is still unchecked rests on that record's
    /// stamp, so two base theorems citing each other would each pass with
    /// the other resident (`theorem pa : ∀ p, p := pb`, `theorem pb := pa`).
    /// The only cycles Lean's kernel builds are an inductive family's own
    /// (a type and its constructors, a recursor's ι-rules citing the
    /// recursor, a mutual block); a cycle through any other record, a
    /// self-citation included, refuses as [`ReferenceRefusal::BaseRecheck`].
    fn recheck_base_closure(&self, root: &Name) -> Result<(), ReferenceRefusal> {
        let mut done = self
            .rechecked
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if done.contains(root) {
            return Ok(());
        }
        // Iterative post-order: (name, children pushed?). `path` is the
        // chain of records being expanded, root first.
        let mut path: Vec<Name> = Vec::new();
        let mut on_path: HashSet<Name> = HashSet::new();
        let mut stack: Vec<(Name, bool)> = vec![(root.clone(), false)];
        while let Some((n, expanded)) = stack.pop() {
            if done.contains(&n) {
                continue;
            }
            if expanded {
                path.pop();
                on_path.remove(&n);
                self.recheck_one(&n)?;
                done.insert(n);
                continue;
            }
            if on_path.contains(&n) {
                // Not reachable (a back edge is refused when it is found
                // below); refused the same way anyway.
                self.refuse_cycle(&path, &n)?;
                continue;
            }
            path.push(n.clone());
            on_path.insert(n.clone());
            stack.push((n.clone(), true));
            let mut deps: Vec<Name> = base_edges(&self.env, &n)
                .into_iter()
                .filter(|d| {
                    self.base.contains(d) && !self.admitted.contains(d) && !done.contains(d)
                })
                .collect();
            deps.sort_by_cached_key(Name::to_string);
            let mut fresh: Vec<Name> = Vec::with_capacity(deps.len());
            for d in deps {
                if on_path.contains(&d) {
                    self.refuse_cycle(&path, &d)?;
                } else {
                    fresh.push(d);
                }
            }
            stack.extend(fresh.into_iter().rev().map(|d| (d, false)));
        }
        Ok(())
    }

    /// `path` ends at a record that cites `back`, which is on `path`: the
    /// cycle is `back ..= path.last()`. Admitted only when every member is a
    /// record of an inductive family or a quotient primitive.
    fn refuse_cycle(&self, path: &[Name], back: &Name) -> Result<(), ReferenceRefusal> {
        let start = path.iter().position(|p| p == back).unwrap_or(0);
        let cycle = &path[start..];
        let family = |n: &Name| {
            self.env.get_inductive(n).is_some()
                || self.env.get_constructor(n).is_some()
                || self.env.get_recursor(n).is_some()
                || self.env.get_quot(n).is_some()
        };
        match cycle.iter().find(|n| !family(n)) {
            None => Ok(()),
            Some(member) => {
                let shown: Vec<String> = cycle
                    .iter()
                    .chain(std::iter::once(back))
                    .map(Name::to_string)
                    .collect();
                Err(ReferenceRefusal::BaseRecheck {
                    decl: member.clone(),
                    reason: format!(
                        "its citation closure is cyclic ({}), so a dependencies-first \
                         re-check would rest on an unchecked stamp",
                        shown.join(" → ")
                    ),
                })
            }
        }
    }

    /// Re-check one base record in the entry's settings. What it covers: a
    /// value-bearing constant's value against its type (a value citing the
    /// constant itself is a cycle, refused by `recheck_base_closure` before
    /// this runs); every other record's type as a well-formed type; a
    /// recursor's metadata and the subject reduction of each ι-rule; a
    /// foundational axiom's or quotient primitive's canonical statement AND
    /// the premises it names (`Environment::check_foundation_premises`); any
    /// other axiom refuses; and, for a record of an inductive family, the
    /// family's whole admission re-run by the kernel (`recheck_family_block`,
    /// R161: positivity and universe checks included).
    fn recheck_one(&self, name: &Name) -> Result<(), ReferenceRefusal> {
        let fail = |reason: String| ReferenceRefusal::BaseRecheck {
            decl: name.clone(),
            reason,
        };
        let kernel = |e: EnvError| fail(e.to_string());
        let type_only = |level_params: &[Name], type_: &Expr| {
            self.env
                .check_decl_readonly_strict(&Declaration::Axiom {
                    name: name.clone(),
                    level_params: level_params.to_vec(),
                    type_: type_.clone(),
                })
                .map_err(kernel)
        };
        if let Some(info) = self.env.get_const(name) {
            if info.kind == ConstantKind::Axiom {
                if !is_canonical_foundational_constant(info) {
                    // `outside_ax0` (or the tripwire closure) refuses a cited
                    // closure that reaches this first; a closure the re-check
                    // reaches that those missed still never rests on it.
                    return Err(fail("an axiom outside Ax0".to_string()));
                }
                self.env.check_foundation_premises(name).map_err(fail)?;
                type_only(&info.level_params, &info.type_)?;
            } else if let Some(value) = &info.value {
                let decl = match info.kind {
                    ConstantKind::Theorem => Declaration::Theorem {
                        name: name.clone(),
                        level_params: info.level_params.clone(),
                        type_: info.type_.clone(),
                        value: value.clone(),
                    },
                    ConstantKind::Opaque => Declaration::Opaque {
                        name: name.clone(),
                        level_params: info.level_params.clone(),
                        type_: info.type_.clone(),
                        value: value.clone(),
                    },
                    ConstantKind::Definition | ConstantKind::Axiom => Declaration::Definition {
                        name: name.clone(),
                        level_params: info.level_params.clone(),
                        type_: info.type_.clone(),
                        value: value.clone(),
                        is_reducible: info.is_reducible,
                    },
                };
                self.env.check_decl_readonly_strict(&decl).map_err(kernel)?;
            } else {
                type_only(&info.level_params, &info.type_)?;
            }
        }
        if let Some(i) = self.env.get_inductive(name) {
            type_only(&i.level_params, &i.type_)?;
        }
        self.recheck_family_block(name).map_err(fail)?;
        if let Some(c) = self.env.get_constructor(name) {
            type_only(&c.level_params, &c.type_)?;
        }
        if self.env.get_recursor(name).is_some() {
            self.env
                .authenticate_recursor_readonly(name)
                .map_err(fail)?;
        }
        if let Some(q) = self.env.get_quot(name) {
            let canonical = crate::quot::init_quot_vals()
                .into_iter()
                .find(|v| v.name == *name);
            match canonical {
                Some(v) if v.level_params.len() == q.level_params.len() && v.type_ == q.type_ => {}
                _ => return Err(fail("not the kernel's quotient primitive".to_string())),
            }
            self.env.check_foundation_premises(name).map_err(fail)?;
        }
        Ok(())
    }

    /// Re-run, once per block, the kernel's admission of the base inductive
    /// family `name` belongs to (an inductive type, a constructor or a
    /// recursor of it; anything else is a no-op): positivity, constructor
    /// shape, block agreement, universe constraints and the well-typedness of
    /// every type and constructor, in this entry's theory, mode and settings,
    /// with every resident member compared to the one the kernel generates
    /// (`Environment::reference_recheck_inductive_block`, R161). A family's
    /// records carry `FullKernelCheck` from wherever the base built them, so
    /// without this a non-positive or universe-inconsistent family stamped
    /// in the base would be cited on its stamp.
    fn recheck_family_block(&self, name: &Name) -> Result<(), String> {
        let family = if let Some(i) = self.env.get_inductive(name) {
            i.all_names.first().cloned().unwrap_or_else(|| name.clone())
        } else if let Some(c) = self.env.get_constructor(name) {
            c.inductive_name.clone()
        } else if let Some(r) = self.env.get_recursor(name) {
            r.inductive_name.clone()
        } else {
            return Ok(());
        };
        let head = self
            .env
            .get_inductive(&family)
            .and_then(|i| i.all_names.first().cloned())
            .unwrap_or_else(|| family.clone());
        let mut done = self
            .replayed_blocks
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !done.contains_key(&head) {
            let generated = self
                .env
                .reference_recheck_inductive_block(&head)
                .map_err(|e| format!("its inductive family does not re-admit: {e}"))?;
            done.insert(head.clone(), generated);
        }
        // Membership (R161, review): the replay compares only the members the
        // block's own lists name, so a record the block does not generate
        // (a type whose `all_names` points at another block, a constructor
        // missing from its type's `constructor_names`, a recursor whose name
        // is not `<ty>.rec`) would otherwise be cited on its stamp alone.
        // Lean's replay refuses such a record ("No such constructor" / "No
        // such recursor"); so does this.
        let generated = done.get(&head).cloned().unwrap_or_default();
        drop(done);
        if generated.contains(name) {
            return Ok(());
        }
        // `<ty>.casesOn` / `<ty>.recOn` recursor-table entries: the replay
        // admits without generating them, so each is compared with the one
        // the kernel's builders generate from the family instead.
        match self.env.reference_recheck_aux_eliminator(name) {
            Ok(None) => {}
            Ok(Some(ty)) if generated.contains(&ty) => return Ok(()),
            Ok(Some(ty)) => {
                return Err(format!(
                    "its inductive family does not re-admit: `{name}` eliminates `{ty}`, \
                     which the block of `{head}` does not generate"
                ))
            }
            Err(e) => {
                return Err(format!(
                    "its inductive family does not re-admit: `{name}` is not the kernel's \
                     auxiliary eliminator: {e}"
                ))
            }
        }
        Err(format!(
            "its inductive family does not re-admit: the block of `{head}` does not \
             generate `{name}`"
        ))
    }

    /// Name a kernel refusal (module docs, "Refusals").
    fn classify(&self, err: EnvError, exprs: &[Expr]) -> ReferenceRefusal {
        if !matches!(err, EnvError::TypeCheckFailed { .. }) {
            return ReferenceRefusal::Kernel(err);
        }
        match excluded_reducer_in_closure(&self.env, exprs) {
            Some(exclusion) => ReferenceRefusal::TheoryExclusion(exclusion),
            None => ReferenceRefusal::Kernel(err),
        }
    }
}

/// Classify every checker setting of `base` (module docs). ONE destructuring
/// with no rest pattern: a new field of [`CheckerSettings`] does not compile
/// until it is classified here.
fn check_settings(base: &Environment) -> Result<(), ReferenceRefusal> {
    let CheckerSettings {
        // Forced by `new` (and re-read after forcing).
        mode: _,
        kernel_theory: _,
        // LeanReferenceV1 is the existing4.30 profile. Supporting another
        // source profile requires a separately identified reference theory.
        lean_level_profile,
        // Not Lean's: refuse, now or ever.
        cumulative,
        cumulative_ever,
        // A budget, a cache bound, an observer: none can turn a refusal into
        // an acceptance.
        max_heartbeats: _,
        max_cache_entries: _,
        profile_heartbeats: _,
    } = base.checker_settings();
    if lean_level_profile != crate::level::LeanLevelProfile::Lean430 {
        return Err(ReferenceRefusal::NonLeanSetting {
            setting: "lean_level_profile",
        });
    }
    if cumulative || cumulative_ever {
        return Err(ReferenceRefusal::NonLeanSetting {
            setting: "cumulative",
        });
    }
    Ok(())
}

/// The base's citation edges, reversed, over Lean's `CollectAxioms` edges: a
/// constant's type and value, a recursor's type and rules, and an inductive
/// type to each of its constructors.
struct CitationGraph {
    rev: std::collections::HashMap<Name, Vec<Name>>,
    /// Every tripwire the base holds or cites.
    tripwire_seeds: Vec<Name>,
}

impl CitationGraph {
    fn of(base: &Environment) -> Self {
        let mut rev: std::collections::HashMap<Name, Vec<Name>> = std::collections::HashMap::new();
        let mut seeds: Vec<Name> = Vec::new();
        let mut edge = |from: &Name, e: &Expr, seeds: &mut Vec<Name>| {
            let mut cited = HashSet::new();
            e.used_constants_dag(UsedConstants::WithProjectionStructures, &mut cited);
            for c in cited {
                if is_tripwire(&c) {
                    seeds.push(c.clone());
                }
                rev.entry(c).or_default().push(from.clone());
            }
        };
        for c in base.constants() {
            if is_tripwire(&c.name) {
                seeds.push(c.name.clone());
            }
            edge(&c.name, &c.type_, &mut seeds);
            if let Some(v) = &c.value {
                edge(&c.name, v, &mut seeds);
            }
        }
        for r in base.recursors() {
            edge(&r.name, &r.type_, &mut seeds);
            for rule in &r.rules {
                edge(&r.name, &rule.rhs, &mut seeds);
            }
        }
        // An inductive type reaches its constructors (Lean's `CollectAxioms`
        // visits `ctors` of an `inductInfo`): citing `T` alone reaches what
        // `T.mk`'s type cites.
        for i in base.inductives() {
            for ctor in &i.constructor_names {
                rev.entry(ctor.clone()).or_default().push(i.name.clone());
            }
        }
        seeds.sort_by_cached_key(Name::to_string);
        seeds.dedup();
        Self {
            rev,
            tripwire_seeds: seeds,
        }
    }

    /// Every constant whose closure reaches one of `seeds`, with one seed it
    /// reaches. Propagated backwards in seed-name order, so the answer does
    /// not depend on hash order.
    fn taint(&self, mut seeds: Vec<Name>) -> std::collections::HashMap<Name, Name> {
        seeds.sort_by_cached_key(Name::to_string);
        seeds.dedup();
        let mut tainted: std::collections::HashMap<Name, Name> = std::collections::HashMap::new();
        for seed in seeds {
            let mut stack = vec![seed.clone()];
            while let Some(n) = stack.pop() {
                if tainted.contains_key(&n) {
                    continue;
                }
                tainted.insert(n.clone(), seed.clone());
                if let Some(users) = self.rev.get(&n) {
                    stack.extend(users.iter().filter(|u| !tainted.contains_key(*u)).cloned());
                }
            }
        }
        tainted
    }
}

/// The base's axioms outside Ax0 and the quotient formers: every `Axiom`-kind
/// constant that is not a tripwire (refused by its own, more specific rule)
/// and is not the kernel's canonical foundational constant of its name
/// (`is_canonical_foundational_constant`: name AND statement) over the
/// premises its statement names (`Environment::check_foundation_premises`:
/// `Iff`, `Eq`, `Nonempty` are Lean's inductives in this base), plus every
/// quotient primitive whose `Eq` is not.
fn outside_ax0_axioms(base: &Environment) -> Vec<Name> {
    let axioms = base.constants().filter(|c| {
        c.kind == ConstantKind::Axiom
            && !is_tripwire(&c.name)
            && !(is_canonical_foundational_constant(c)
                && base.check_foundation_premises(&c.name).is_ok())
    });
    let quotients = base
        .quotients()
        .filter(|q| base.check_foundation_premises(&q.name).is_err());
    axioms
        .map(|c| c.name.clone())
        .chain(quotients.map(|q| q.name.clone()))
        .collect()
}

/// What base record `name` cites, over the edges of [`CitationGraph`]
/// (forward): its type and value, a recursor's type and rules, an inductive
/// type's constructors.
fn base_edges(env: &Environment, name: &Name) -> HashSet<Name> {
    let mut out = HashSet::new();
    if let Some(info) = env.get_const(name) {
        info.type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut out);
        if let Some(v) = &info.value {
            v.used_constants_dag(UsedConstants::WithProjectionStructures, &mut out);
        }
    }
    if let Some(r) = env.get_recursor(name) {
        r.type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut out);
        for rule in &r.rules {
            rule.rhs
                .used_constants_dag(UsedConstants::WithProjectionStructures, &mut out);
        }
    }
    if let Some(i) = env.get_inductive(name) {
        out.extend(i.constructor_names.iter().cloned());
    }
    if let Some(c) = env.get_constructor(name) {
        c.type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut out);
    }
    out
}

/// The tripwire closure of `base` (the unit tests' handle on it).
#[cfg(test)]
fn tripwire_taint(base: &Environment) -> std::collections::HashMap<Name, Name> {
    let graph = CitationGraph::of(base);
    graph.taint(graph.tripwire_seeds.clone())
}

fn decl_parts(d: &Declaration) -> (&Name, &Expr, Option<&Expr>) {
    match d {
        Declaration::Definition {
            name, type_, value, ..
        }
        | Declaration::Theorem {
            name, type_, value, ..
        }
        | Declaration::Opaque {
            name, type_, value, ..
        } => (name, type_, Some(value)),
        Declaration::Axiom { name, type_, .. } => (name, type_, None),
    }
}

/// Whether `name` passed the full kernel check in `env` (module docs).
fn provenance_full(env: &Environment, name: &Name) -> bool {
    if env.constant_needs_recheck(name) {
        return false;
    }
    env.declaration_verification(name) == Some(DeclarationVerification::FullKernelCheck)
}

/// The first registered native reducer, by name, in the δ-closure of `exprs`
/// that Lean's profile excludes, and why.
fn excluded_reducer_in_closure(env: &Environment, exprs: &[Expr]) -> Option<LeanTheoryExclusion> {
    let mut frontier: HashSet<Name> = HashSet::new();
    for e in exprs {
        e.used_constants_dag(UsedConstants::ConstantsOnly, &mut frontier);
    }
    let mut visited: HashSet<Name> = HashSet::new();
    let mut stack: Vec<Name> = frontier.into_iter().collect();
    let mut hits: Vec<(String, LeanTheoryExclusion)> = Vec::new();
    while let Some(c) = stack.pop() {
        if !visited.insert(c.clone()) {
            continue;
        }
        if visited.len() > CLASSIFY_CLOSURE_CAP {
            break;
        }
        if env.get_native_reducer(&c).is_some() && !Environment::is_lean_kernel_nat_extension(&c) {
            if let Some(exclusion) = env.lean_theory_exclusion(&c) {
                hits.push((c.to_string(), exclusion));
            }
        }
        if let Some(info) = env.get_const(&c) {
            if info.kind == ConstantKind::Definition {
                if let Some(body) = info.value.as_ref() {
                    let mut next = HashSet::new();
                    body.used_constants_dag(UsedConstants::ConstantsOnly, &mut next);
                    stack.extend(next.into_iter().filter(|n| !visited.contains(n)));
                }
            }
        }
    }
    hits.sort_by(|a, b| a.0.cmp(&b.0));
    hits.into_iter().next().map(|(_, exclusion)| exclusion)
}

/// A DAG walk (shared subterms visited once, by address) for the first
/// non-Lean expression form.
#[derive(Default)]
struct KindWalk {
    seen: HashSet<usize>,
}

impl KindWalk {
    fn first_non_lean(&mut self, root: &Expr) -> Option<NonLeanKind> {
        let mut stack: Vec<&Expr> = vec![root];
        while let Some(e) = stack.pop() {
            if !self.seen.insert(std::ptr::from_ref(e) as usize) {
                continue;
            }
            // ONE match, no wildcard arm: a new `ExprKind` variant does not
            // compile until it is classified here as Lean or non-Lean.
            let kind = match e.kind() {
                ExprKind::BVar(_)
                | ExprKind::FVar(_)
                | ExprKind::Sort(_)
                | ExprKind::Const(..)
                | ExprKind::Lit(_) => continue,
                ExprKind::App(f, a) => {
                    stack.push(f);
                    stack.push(a);
                    continue;
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    stack.push(ty);
                    stack.push(body);
                    continue;
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    stack.push(ty);
                    stack.push(val);
                    stack.push(body);
                    continue;
                }
                ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                    stack.push(inner);
                    continue;
                }
                ExprKind::SProp => NonLeanKind::SProp,
                ExprKind::Squash(_) => NonLeanKind::Squash,
                ExprKind::CubicalInterval => NonLeanKind::CubicalInterval,
                ExprKind::CubicalI0 => NonLeanKind::CubicalI0,
                ExprKind::CubicalI1 => NonLeanKind::CubicalI1,
                ExprKind::CubicalPath { .. } => NonLeanKind::CubicalPath,
                ExprKind::CubicalPathLam { .. } => NonLeanKind::CubicalPathLam,
                ExprKind::CubicalPathApp { .. } => NonLeanKind::CubicalPathApp,
                ExprKind::CubicalHComp { .. } => NonLeanKind::CubicalHComp,
                ExprKind::CubicalTransp { .. } => NonLeanKind::CubicalTransp,
                ExprKind::CubicalCoe { .. } => NonLeanKind::CubicalCoe,
                ExprKind::ZFCSet(_) => NonLeanKind::ZFCSet,
                ExprKind::ZFCMem { .. } => NonLeanKind::ZFCMem,
                ExprKind::ZFCComprehension { .. } => NonLeanKind::ZFCComprehension,
            };
            return Some(kind);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{BinderInfo, ZFCSetExpr};
    use crate::level::Level;

    fn name(s: &str) -> Name {
        Name::from_string(s)
    }

    /// The defence in depth behind `check_terms`: a cited constant this entry
    /// has not walked is walked, and checked for provenance, at citation
    /// time. Unreachable from outside the module (every constant in the
    /// environment was walked by `new` or admitted by `add_checked`), so the
    /// kernel is assembled here with one constant deliberately left out of
    /// `walked`. Controls: the same citation shape of a walked constant is
    /// accepted, and the unwalked constants are exactly what the base walk
    /// itself refuses.
    #[test]
    fn test_citation_of_an_unwalked_constant_is_checked_at_citation() {
        let mut env = Environment::with_mode(CleanMode::SetTheoretic);
        env.add_decl(Declaration::Axiom {
            name: name("ZFC.Set"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("ZFC.Set");
        env.add_decl(Declaration::Definition {
            name: name("kr0_bad"),
            level_params: vec![],
            type_: Expr::const_(name("ZFC.Set"), vec![]),
            value: Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty)),
            is_reducible: false,
        })
        .expect("kr0_bad in its own theory");
        env.add_decl_structural(Declaration::Axiom {
            name: name("kr0_structural"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("structural axiom");
        env.add_decl(Declaration::Axiom {
            name: name("kr0_good"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("kr0_good");
        assert!(matches!(
            ReferenceKernel::new(env.clone()),
            Err(ReferenceRefusal::NonLeanExprKind { .. }
                | ReferenceRefusal::StructuralProvenance { .. })
        ));
        let walked: HashSet<Name> = env
            .constants()
            .map(|c| c.name.clone())
            .filter(|n| n != &name("kr0_bad") && n != &name("kr0_structural"))
            .collect();
        env.set_kernel_theory(KernelTheory::LeanReference);
        env.force_mode_for_reference_entry(CleanMode::Constructive);
        let mut k = ReferenceKernel {
            env,
            theory_id: TheoryId::LeanReferenceV1,
            env_digest: EnvDigest([0; 32]),
            walked,
            admitted: HashSet::new(),
            tainted: std::collections::HashMap::new(),
            // Hand-built past `new`: no Ax0 closure and no base re-check, so
            // this exercises the citation-time walk alone.
            outside_ax0: std::collections::HashMap::new(),
            base: HashSet::new(),
            rechecked: std::sync::Mutex::new(HashSet::new()),
            replayed_blocks: std::sync::Mutex::new(std::collections::HashMap::new()),
        };
        let citer = |n: &str, ty: Expr, cited: &str| Declaration::Definition {
            name: name(n),
            level_params: vec![],
            type_: ty,
            value: Expr::const_(name(cited), vec![]),
            is_reducible: false,
        };
        let set = Expr::const_(name("ZFC.Set"), vec![]);
        let err = k
            .add_checked(citer("kr0_c1", set, "kr0_bad"))
            .expect_err("the cited constant's ZFCSet value refuses");
        assert!(
            matches!(&err, ReferenceRefusal::NonLeanExprKind { decl, kind: NonLeanKind::ZFCSet }
                if *decl == name("kr0_bad")),
            "got {err:?}"
        );
        let err = k
            .add_checked(citer(
                "kr0_c2",
                Expr::const_(name("kr0_structural"), vec![]),
                "kr0_structural_pf",
            ))
            .expect_err("a structural cited constant refuses");
        assert!(
            matches!(&err, ReferenceRefusal::StructuralProvenance { decl }
                if *decl == name("kr0_structural")),
            "got {err:?}"
        );
        // Control.
        let prop_of_good = Expr::pi(
            BinderInfo::Default,
            Expr::const_(name("kr0_good"), vec![]),
            Expr::const_(name("kr0_good"), vec![]),
        );
        k.add_checked(Declaration::Definition {
            name: name("kr0_c3"),
            level_params: vec![],
            type_: Expr::prop(),
            value: prop_of_good,
            is_reducible: false,
        })
        .expect("citing a walked constant is accepted");
    }

    /// The base closure follows a recursor's RULES, not only its type: a
    /// base handed in by value may carry a recursor whose ι-rule rhs cites a
    /// tripwire its type does not (an honest kernel never generates one, so
    /// it is planted here with `register_recursor`, which keeps the
    /// constant's type and replaces the rules). Control: the same base with
    /// the kernel's own rule leaves the recursor untainted.
    #[test]
    fn test_taint_follows_a_recursor_rule() {
        let mut env = Environment::default();
        env.add_decl(Declaration::Axiom {
            name: name("sorryAx"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("a tripwire axiom");
        env.add_inductive_core(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![crate::inductive::InductiveType {
                name: name("KR1R"),
                type_: Expr::prop(),
                constructors: vec![crate::inductive::Constructor {
                    name: name("KR1R.mk"),
                    type_: Expr::const_(name("KR1R"), vec![]),
                }],
            }],
        })
        .expect("KR1R");
        let rec = name("KR1R.rec");
        assert!(
            !tripwire_taint(&env).contains_key(&rec),
            "control: the kernel's own recursor reaches no tripwire"
        );
        let mut doctored = env.get_recursor(&rec).expect("KR1R.rec").clone();
        doctored.rules[0].rhs = Expr::const_(name("sorryAx"), vec![]);
        env.register_recursor(doctored);
        assert_eq!(
            tripwire_taint(&env).get(&rec),
            Some(&name("sorryAx")),
            "a rule citing a tripwire taints its recursor"
        );
    }

    /// The post-admission fence (`admit_generated`): a member the kernel
    /// generated joins the checked set only when it carries the full-check
    /// stamp and holds no non-Lean form. Unreachable from outside the module
    /// (the kernel's own generators stamp and build Lean forms), so the
    /// members are planted here directly. Control: a stamped, Lean-form member
    /// is admitted and joins both sets; the refused ones join neither.
    #[test]
    fn test_admit_generated_refuses_unstamped_and_non_lean_members() {
        let mut env = Environment::with_mode(CleanMode::SetTheoretic);
        env.add_decl(Declaration::Axiom {
            name: name("ZFC.Set"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("ZFC.Set");
        env.add_decl(Declaration::Definition {
            name: name("kr1_gen_bad"),
            level_params: vec![],
            type_: Expr::const_(name("ZFC.Set"), vec![]),
            value: Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty)),
            is_reducible: false,
        })
        .expect("a non-Lean form in its own theory");
        env.add_decl_structural(Declaration::Axiom {
            name: name("kr1_gen_structural"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("structural axiom");
        env.add_decl(Declaration::Axiom {
            name: name("kr1_gen_good"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("kr1_gen_good");
        env.set_kernel_theory(KernelTheory::LeanReference);
        env.force_mode_for_reference_entry(CleanMode::Constructive);
        let mut k = ReferenceKernel {
            env,
            theory_id: TheoryId::LeanReferenceV1,
            env_digest: EnvDigest([0; 32]),
            walked: HashSet::new(),
            admitted: HashSet::new(),
            tainted: std::collections::HashMap::new(),
            // Hand-built past `new`: no Ax0 closure and no base re-check, so
            // this exercises the citation-time walk alone.
            outside_ax0: std::collections::HashMap::new(),
            base: HashSet::new(),
            rechecked: std::sync::Mutex::new(HashSet::new()),
            replayed_blocks: std::sync::Mutex::new(std::collections::HashMap::new()),
        };
        let err = k
            .admit_generated(&[name("kr1_gen_structural")])
            .expect_err("an unstamped member refuses");
        assert!(
            matches!(&err, ReferenceRefusal::StructuralProvenance { decl }
                if *decl == name("kr1_gen_structural")),
            "got {err:?}"
        );
        let err = k
            .admit_generated(&[name("kr1_gen_bad")])
            .expect_err("a non-Lean member refuses");
        assert!(
            matches!(&err, ReferenceRefusal::NonLeanExprKind { decl, kind: NonLeanKind::ZFCSet }
                if *decl == name("kr1_gen_bad")),
            "got {err:?}"
        );
        assert!(k.walked.is_empty() && k.admitted.is_empty());
        k.admit_generated(&[name("kr1_gen_good")])
            .expect("a stamped Lean-form member is admitted");
        assert!(k.walked.contains(&name("kr1_gen_good")));
        assert!(k.admitted.contains(&name("kr1_gen_good")));
        assert!(!k.walked.contains(&name("kr1_gen_bad")));
    }

    /// `inductive KR3B : Type | a | b` over an empty base.
    fn two_ctor_base() -> Environment {
        let mut env = Environment::default();
        let t = || Expr::const_(name("KR3B"), vec![]);
        env.add_inductive_core(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![crate::inductive::InductiveType {
                name: name("KR3B"),
                type_: Expr::type_(),
                constructors: vec![
                    crate::inductive::Constructor {
                        name: name("KR3B.a"),
                        type_: t(),
                    },
                    crate::inductive::Constructor {
                        name: name("KR3B.b"),
                        type_: t(),
                    },
                ],
            }],
        })
        .expect("KR3B");
        env
    }

    /// Cite `n` (a constant of the base) as a closed term at its own type,
    /// every universe parameter at `1`.
    fn cite(k: &ReferenceKernel, n: &str) -> Result<ReferenceAccepted, ReferenceRefusal> {
        let env = k.environment();
        let (params, type_) = match (env.get_const(&name(n)), env.get_quot(&name(n))) {
            (Some(info), _) => (info.level_params.clone(), info.type_.clone()),
            (None, Some(q)) => (q.level_params.clone(), q.type_.clone()),
            (None, None) => panic!("{n} is not in the base"),
        };
        let levels = vec![Level::succ(Level::zero()); params.len()];
        let ty = type_.instantiate_level_params_direct(&params, &levels);
        k.check_closed_term(&ty, &Expr::const_(name(n), levels))
    }

    fn expect_recheck(r: Result<ReferenceAccepted, ReferenceRefusal>, want: &str) {
        match r {
            Err(ReferenceRefusal::BaseRecheck { decl, .. }) => assert_eq!(decl, name(want)),
            other => panic!("expected BaseRecheck of {want}, got {other:?}"),
        }
    }

    /// The re-check authenticates a base recursor's ι-rules (R143): a base
    /// whose `KR3B.rec` has its two rules' right-hand sides swapped (so
    /// `KR3B.rec ma mb KR3B.a` would compute `mb`) keeps its stamp, so `new`
    /// takes it, and citing the recursor refuses. Control: the kernel's own
    /// recursor, cited the same way, is accepted.
    #[test]
    fn test_recheck_authenticates_a_base_recursor() {
        let k = ReferenceKernel::new(two_ctor_base()).expect("honest base");
        cite(&k, "KR3B.rec").expect("control: the kernel's recursor re-checks");
        let mut env = two_ctor_base();
        let rec = env.test_recursor_mut(&name("KR3B.rec")).expect("KR3B.rec");
        let first = rec.rules[0].rhs.clone();
        rec.rules[0].rhs = rec.rules[1].rhs.clone();
        rec.rules[1].rhs = first;
        let k = ReferenceKernel::new(env).expect("the stamp survives the doctoring");
        // Since R161 the family's re-admission (which compares the stored
        // recursor with the regenerated one) can reach the forgery first,
        // from whichever family member the post-order re-checks first;
        // `authenticate_recursor_readonly` is the per-record check behind it.
        expect_family_member_recheck(cite(&k, "KR3B.rec"), KR3B_MEMBERS);
        let mut env = two_ctor_base();
        let rec = env.test_recursor_mut(&name("KR3B.rec")).expect("KR3B.rec");
        let first = rec.rules[0].rhs.clone();
        rec.rules[0].rhs = rec.rules[1].rhs.clone();
        rec.rules[1].rhs = first;
        let k = ReferenceKernel::new(env).expect("stamp kept");
        let err = k.recheck_one(&name("KR3B.rec")).map(|()| k.token([0; 32]));
        expect_recheck(err, "KR3B.rec");
    }

    const KR3B_MEMBERS: &[&str] = &["KR3B", "KR3B.a", "KR3B.b", "KR3B.rec"];

    /// A `BaseRecheck` naming one of `members`.
    fn expect_family_member_recheck(
        r: Result<ReferenceAccepted, ReferenceRefusal>,
        members: &[&str],
    ) {
        match r {
            Err(ReferenceRefusal::BaseRecheck { decl, .. })
                if members.iter().any(|m| decl == name(m)) => {}
            other => panic!("expected BaseRecheck of one of {members:?}, got {other:?}"),
        }
    }

    /// The re-check re-checks an inductive's and a constructor's own record
    /// type (the records the kernel's inductive machinery reads, beside the
    /// constant records the checker reads): each doctored to an ill-typed
    /// type refuses at citation. Control: `two_ctor_base` itself (above).
    #[test]
    fn test_recheck_rechecks_inductive_and_constructor_records() {
        let bad = Expr::app(Expr::prop(), Expr::prop());
        let mut env = two_ctor_base();
        env.test_inductive_mut(&name("KR3B")).expect("KR3B").type_ = bad.clone();
        let k = ReferenceKernel::new(env).expect("stamp kept");
        expect_family_member_recheck(cite(&k, "KR3B"), KR3B_MEMBERS);
        let mut env = two_ctor_base();
        env.test_constructor_mut(&name("KR3B.b"))
            .expect("KR3B.b")
            .type_ = bad;
        let k = ReferenceKernel::new(env).expect("stamp kept");
        expect_family_member_recheck(cite(&k, "KR3B.b"), KR3B_MEMBERS);
        let k = ReferenceKernel::new(two_ctor_base()).expect("honest base");
        cite(&k, "KR3B.b").expect("control: the honest constructor re-checks");
    }

    /// A base holding `Eq` (Lean's shape) and the kernel's quotient.
    fn quot_base() -> Environment {
        let mut env = Environment::default();
        let eq = Environment::with_prelude()
            .inductive_decl_of(&name("Eq"))
            .expect("with_prelude has Eq");
        env.add_inductive_core(eq).expect("Eq");
        env.add_quot().expect("Lean's add_quot over Lean's Eq");
        env
    }

    /// The re-check compares a base quotient primitive with the kernel's own
    /// (R143): `Quot.lift`'s record given `Quot.mk`'s statement refuses at
    /// citation. Control: the kernel's own `Quot.lift` is accepted.
    #[test]
    fn test_recheck_compares_a_base_quotient_primitive() {
        let k = ReferenceKernel::new(quot_base()).expect("honest base");
        cite(&k, "Quot.lift").expect("control: the kernel's Quot.lift re-checks");
        let mut env = quot_base();
        let mk = env
            .get_quot(&name("Quot.mk"))
            .expect("Quot.mk")
            .type_
            .clone();
        env.test_quot_mut(&name("Quot.lift"))
            .expect("Quot.lift")
            .type_ = mk;
        let k = ReferenceKernel::new(env).expect("stamp kept");
        expect_recheck(cite(&k, "Quot.lift"), "Quot.lift");
    }

    /// A base constant whose value cites itself is a cycle of length one,
    /// refused before `recheck_one` would check the value with the constant
    /// resident (which passes: `theorem s : ∀ p, p := s`). The record is
    /// planted (an axiom given its own name as value; the stamp of the axiom
    /// stays) because no public door builds it. Control: the public two-cycle
    /// test in `tests/reference_ax0.rs`, and an honest theorem below.
    #[test]
    fn test_recheck_refuses_a_self_citing_base_value() {
        let false_ty = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        let mut env = Environment::default();
        env.add_decl(Declaration::Axiom {
            name: name("kr3_self"),
            level_params: vec![],
            type_: false_ty.clone(),
        })
        .expect("axiom");
        env.add_decl(Declaration::Theorem {
            name: name("kr3_honest"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            ),
        })
        .expect("honest theorem");
        let info = env.test_const_mut(&name("kr3_self")).expect("kr3_self");
        info.kind = ConstantKind::Theorem;
        info.value = Some(Expr::const_(name("kr3_self"), vec![]));
        let k = ReferenceKernel::new(env).expect("no axiom left in the base");
        expect_recheck(
            k.check_closed_term(&false_ty, &Expr::const_(name("kr3_self"), vec![])),
            "kr3_self",
        );
        cite(&k, "kr3_honest").expect("control: an acyclic base theorem");
    }

    /// `recheck_one` refuses an axiom outside Ax0 by itself, not only behind
    /// `outside_ax0` (R143's defence in depth: a closure the re-check reaches
    /// and the taint missed never rests on it), and refuses the canonical
    /// `Classical.choice` over a `Nonempty` that is not Lean's. Controls: the
    /// canonical `Classical.choice` over Lean's `Nonempty` re-checks.
    #[test]
    fn test_recheck_one_refuses_axioms_outside_ax0() {
        let mut env = Environment::default();
        env.add_decl(Declaration::Axiom {
            name: name("kr3_x"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("axiom");
        let nonempty = Environment::with_prelude()
            .inductive_decl_of(&name("Nonempty"))
            .expect("Nonempty");
        env.add_inductive_core(nonempty).expect("Nonempty");
        let choice =
            crate::canonical_foundation_declaration(&name("Classical.choice")).expect("canonical");
        env.add_decl(choice.clone()).expect("choice");
        let k = ReferenceKernel::new(env).expect("a base may hold them");
        expect_recheck(
            k.recheck_one(&name("kr3_x")).map(|()| k.token([0; 32])),
            "kr3_x",
        );
        k.recheck_one(&name("Classical.choice"))
            .expect("control: canonical choice over Lean's Nonempty");

        let mut env = Environment::default();
        env.add_decl(Declaration::Definition {
            name: name("Nonempty"),
            level_params: vec![name("u")],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::sort(Level::param(name("u"))),
                Expr::prop(),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::sort(Level::param(name("u"))),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
                ),
            ),
            is_reducible: false,
        })
        .expect("a definition named Nonempty");
        env.add_decl(choice).expect("choice over it");
        let k = ReferenceKernel::new(env).expect("a base may hold them");
        expect_recheck(
            k.recheck_one(&name("Classical.choice"))
                .map(|()| k.token([0; 32])),
            "Classical.choice",
        );
    }

    /// One inductive block over the current base, no parameters.
    fn add_family(env: &mut Environment, ty: &str, sort: Expr, ctors: &[(&str, Expr)]) {
        env.add_inductive_core(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![crate::inductive::InductiveType {
                name: name(ty),
                type_: sort,
                constructors: ctors
                    .iter()
                    .map(|(n, t)| crate::inductive::Constructor {
                        name: name(n),
                        type_: t.clone(),
                    })
                    .collect(),
            }],
        })
        .unwrap_or_else(|e| panic!("{ty}: {e}"));
    }

    /// A refusal of a member of `family` naming the family's re-admission
    /// (R161), with `why` in its reason. Which member the post-order reaches
    /// first is the closure's business; it is one of `members`.
    fn expect_family_recheck(
        r: Result<ReferenceAccepted, ReferenceRefusal>,
        members: &[&str],
        why: &str,
    ) {
        match r {
            Err(ReferenceRefusal::BaseRecheck { decl, reason }) => {
                assert!(
                    members.iter().any(|m| decl == name(m)),
                    "refused {decl}, not one of {members:?}: {reason}"
                );
                assert!(
                    reason.contains("does not re-admit") && reason.contains(why),
                    "reason {reason:?} does not name `{why}`"
                );
            }
            other => panic!("expected BaseRecheck of {members:?}, got {other:?}"),
        }
    }

    /// `KR1U : Type | u` and `KR1N : Type | mk : (KR1U → KR1N) → KR1N`, a
    /// positive (honest) recursive family.
    fn positive_base() -> Environment {
        let mut env = Environment::default();
        let u = || Expr::const_(name("KR1U"), vec![]);
        let n = || Expr::const_(name("KR1N"), vec![]);
        add_family(&mut env, "KR1U", Expr::type_(), &[("KR1U.u", u())]);
        add_family(
            &mut env,
            "KR1N",
            Expr::type_(),
            &[(
                "KR1N.mk",
                Expr::pi(
                    BinderInfo::Default,
                    Expr::pi(BinderInfo::Default, u(), n()),
                    n(),
                ),
            )],
        );
        env
    }

    /// R161: the base re-check re-runs a family's POSITIVITY. `KR1N.mk`'s
    /// records (the constructor table and the constant table, both stamped
    /// `FullKernelCheck` by the honest admission) are forged to
    /// `(KR1N → KR1N) → KR1N`, a negative occurrence the kernel's admission
    /// refuses. Each record's type is still a well-formed type, so the
    /// per-record re-check R143 shipped passed it (mutant: `recheck_family_block`
    /// returning `Ok(())` turns this test red with `Ok(LeanReferenceV1)`).
    /// Control: the honest family, cited the same way, is accepted, and the
    /// forged family is refused by the kernel when declared afresh.
    #[test]
    fn test_recheck_refuses_a_non_positive_base_family() {
        let k = ReferenceKernel::new(positive_base()).expect("honest base");
        cite(&k, "KR1N.mk").expect("control: the positive family re-admits");
        cite(&k, "KR1N.rec").expect("control: its recursor too");

        let n = || Expr::const_(name("KR1N"), vec![]);
        let forged = Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, n(), n()),
            n(),
        );
        let mut fresh = Environment::default();
        let refused = fresh.add_inductive_core(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![crate::inductive::InductiveType {
                name: name("KR1N"),
                type_: Expr::type_(),
                constructors: vec![crate::inductive::Constructor {
                    name: name("KR1N.mk"),
                    type_: forged.clone(),
                }],
            }],
        });
        assert!(
            refused.is_err(),
            "control: the kernel refuses the forged family afresh"
        );

        let mut env = positive_base();
        env.test_constructor_mut(&name("KR1N.mk"))
            .expect("KR1N.mk")
            .type_ = forged.clone();
        env.test_const_mut(&name("KR1N.mk")).expect("KR1N.mk").type_ = forged;
        let k = ReferenceKernel::new(env).expect("the stamp survives the forging");
        expect_family_recheck(
            cite(&k, "KR1N.mk"),
            &["KR1N", "KR1N.mk"],
            "refused by the kernel",
        );
        expect_family_recheck(
            cite(&k, "KR1N"),
            &["KR1N", "KR1N.mk"],
            "refused by the kernel",
        );
    }

    /// R161: the base re-check re-runs a family's UNIVERSE checks. The
    /// honest `KR1V : Type 1 | mk : Type → KR1V` has its type records (the
    /// inductive value and the constant) forged to `Type`, so a `Type 0`
    /// family carries a `Type` field, which the kernel's admission refuses.
    /// Every record's type is still well formed (R143's per-record check
    /// passed it; same mutant as above). Control: the honest family is
    /// accepted.
    #[test]
    fn test_recheck_refuses_a_universe_inconsistent_base_family() {
        let base = || {
            let mut env = Environment::default();
            let v = Expr::const_(name("KR1V"), vec![]);
            add_family(
                &mut env,
                "KR1V",
                Expr::sort(Level::succ(Level::succ(Level::zero()))),
                &[("KR1V.mk", Expr::pi(BinderInfo::Default, Expr::type_(), v))],
            );
            env
        };
        let k = ReferenceKernel::new(base()).expect("honest base");
        cite(&k, "KR1V.mk").expect("control: the honest family re-admits");

        let mut env = base();
        env.test_inductive_mut(&name("KR1V")).expect("KR1V").type_ = Expr::type_();
        env.test_const_mut(&name("KR1V")).expect("KR1V").type_ = Expr::type_();
        let k = ReferenceKernel::new(env).expect("the stamp survives the forging");
        expect_family_recheck(
            cite(&k, "KR1V.mk"),
            &["KR1V", "KR1V.mk"],
            "refused by the kernel",
        );
    }

    /// R161: the two fields the `.olean` replay leaves to its loader are
    /// compared too. `KR1P : Prop | a | b` eliminates only into `Prop`; its
    /// inductive value forged to `is_large_elim = true` refuses, and so does
    /// a type constant record that disagrees with the inductive value.
    /// Control: the honest family is accepted. Mutant: either comparison
    /// removed turns its half red.
    #[test]
    fn test_recheck_compares_large_elim_and_the_type_constant() {
        let base = || {
            let mut env = Environment::default();
            let p = || Expr::const_(name("KR1P"), vec![]);
            add_family(
                &mut env,
                "KR1P",
                Expr::prop(),
                &[("KR1P.a", p()), ("KR1P.b", p())],
            );
            env
        };
        let k = ReferenceKernel::new(base()).expect("honest base");
        cite(&k, "KR1P.a").expect("control: the honest family re-admits");

        let mut env = base();
        let ind = env.test_inductive_mut(&name("KR1P")).expect("KR1P");
        assert!(
            !ind.is_large_elim,
            "control: the kernel computed small elimination"
        );
        ind.is_large_elim = true;
        let k = ReferenceKernel::new(env).expect("stamp kept");
        expect_family_recheck(
            cite(&k, "KR1P.a"),
            &["KR1P", "KR1P.a"],
            "large-elimination flag",
        );

        let mut env = base();
        let pi = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
        env.test_const_mut(&name("KR1P")).expect("KR1P").type_ = pi;
        let k = ReferenceKernel::new(env).expect("stamp kept");
        let r = cite(&k, "KR1P.a");
        assert!(
            matches!(&r, Err(ReferenceRefusal::BaseRecheck { .. })),
            "a type constant record disagreeing with its inductive value refuses: {r:?}"
        );
    }

    /// R161 (review): the forgery only the type-constant comparison catches.
    /// The `Prop → Prop` forgery above also trips a debug assertion in
    /// `infer`, so it does not show the comparison is needed in a build
    /// without debug assertions. Here the DATA family `KR3B : Type | a | b`
    /// has its constant record forged to `Prop`, which would make `KR3B.a`
    /// and `KR3B.b` proof-irrelevant and so definitionally equal. Mutant: the
    /// constant comparison removed accepts this as `Ok(LeanReferenceV1)`.
    /// Control: the honest family is accepted.
    #[test]
    fn test_recheck_refuses_a_data_family_whose_constant_says_prop() {
        let k = ReferenceKernel::new(two_ctor_base()).expect("honest base");
        cite(&k, "KR3B.a").expect("control: the honest data family re-admits");
        let mut env = two_ctor_base();
        env.test_const_mut(&name("KR3B")).expect("KR3B").type_ = Expr::prop();
        let k = ReferenceKernel::new(env).expect("stamp kept");
        expect_family_recheck(cite(&k, "KR3B.a"), KR3B_MEMBERS, "constant-table entry");
    }

    /// R161: the type constant's universe parameters are compared, not only
    /// its type. `KR1S.{u, v} : Sort (max (u+1) (v+1)) | mk` with the
    /// constant record's parameters swapped to `[v, u]` keeps a type that is
    /// the same expression and, instantiated, a defeq sort, so nothing else
    /// reads a difference; the constant table and the inductive value still
    /// disagree about which argument is which. Mutant: the `level_params`
    /// clause dropped accepts it. Control: the honest family is accepted.
    #[test]
    fn test_recheck_compares_the_type_constants_universe_parameters() {
        let base = || {
            let mut env = Environment::default();
            let u = Level::param(name("u"));
            let v = Level::param(name("v"));
            env.add_inductive_core(InductiveDecl {
                level_params: vec![name("u"), name("v")],
                num_params: 0,
                types: vec![crate::inductive::InductiveType {
                    name: name("KR1S"),
                    type_: Expr::sort(Level::max(Level::succ(u.clone()), Level::succ(v.clone()))),
                    constructors: vec![crate::inductive::Constructor {
                        name: name("KR1S.mk"),
                        type_: Expr::const_(name("KR1S"), vec![u, v]),
                    }],
                }],
            })
            .expect("KR1S");
            env
        };
        let k = ReferenceKernel::new(base()).expect("honest base");
        cite(&k, "KR1S.mk").expect("control: the honest family re-admits");
        let mut env = base();
        env.test_const_mut(&name("KR1S"))
            .expect("KR1S")
            .level_params = vec![name("v"), name("u")];
        let k = ReferenceKernel::new(env).expect("stamp kept");
        expect_family_recheck(
            cite(&k, "KR1S.mk"),
            &["KR1S", "KR1S.mk"],
            "constant-table entry",
        );
    }

    /// R161: a family's `casesOn` / `recOn` recursor-table entries (which the
    /// block replay admits without) are compared with the ones the kernel's
    /// builders generate. `KR3B.casesOn` with its two rules' right-hand sides
    /// swapped is refused naming the auxiliary-eliminator comparison; the
    /// honest `KR3B.casesOn` and `KR3B.recOn` are accepted. Mutant: that
    /// comparison skipped leaves only the per-record subject-reduction check,
    /// whose refusal does not name it.
    #[test]
    fn test_recheck_compares_aux_eliminators_with_the_generated_ones() {
        // `add_inductive` (not `_core`): the admission that generates
        // `casesOn` / `recOn`.
        let two_ctor_base = || {
            let mut env = Environment::default();
            let t = || Expr::const_(name("KR3B"), vec![]);
            env.add_inductive(InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![crate::inductive::InductiveType {
                    name: name("KR3B"),
                    type_: Expr::type_(),
                    constructors: vec![
                        crate::inductive::Constructor {
                            name: name("KR3B.a"),
                            type_: t(),
                        },
                        crate::inductive::Constructor {
                            name: name("KR3B.b"),
                            type_: t(),
                        },
                    ],
                }],
            })
            .expect("KR3B with its auxiliary eliminators");
            env
        };
        let k = ReferenceKernel::new(two_ctor_base()).expect("honest base");
        for honest in ["KR3B.casesOn", "KR3B.recOn"] {
            assert!(
                k.environment().get_recursor(&name(honest)).is_some(),
                "{honest} is a recursor-table entry"
            );
            cite(&k, honest).unwrap_or_else(|e| panic!("control {honest}: {e:?}"));
        }
        let mut env = two_ctor_base();
        let rec = env
            .test_recursor_mut(&name("KR3B.casesOn"))
            .expect("KR3B.casesOn");
        let first = rec.rules[0].rhs.clone();
        rec.rules[0].rhs = rec.rules[1].rhs.clone();
        rec.rules[1].rhs = first;
        let k = ReferenceKernel::new(env).expect("stamp kept");
        let r = k
            .recheck_one(&name("KR3B.casesOn"))
            .map(|()| k.token([0; 32]));
        expect_family_recheck(r, &["KR3B.casesOn"], "auxiliary eliminator");
    }

    /// R161 (review probe A): a type whose `all_names` names another block
    /// is not re-admitted through that block. `KR1N.mk` is forged
    /// non-positive as above AND `KR1N`'s `all_names` is pointed at the
    /// honest `[KR1U]`, so the re-check would replay `KR1U`'s block alone;
    /// the block does not generate `KR1N` or `KR1N.mk`, and the re-check
    /// refuses both. The same with the constructor's `inductive_name`
    /// pointed at `KR1U` (probe C). Mutant: the membership check removed
    /// accepts both citations as `Ok(LeanReferenceV1)`. Control: the
    /// forgery without the redirect is refused by positivity, and the honest
    /// base is accepted (`test_recheck_refuses_a_non_positive_base_family`).
    #[test]
    fn test_recheck_refuses_a_member_its_block_does_not_generate() {
        let n = || Expr::const_(name("KR1N"), vec![]);
        let forged = Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, n(), n()),
            n(),
        );
        let forge = || {
            let mut env = positive_base();
            env.test_constructor_mut(&name("KR1N.mk"))
                .expect("KR1N.mk")
                .type_ = forged.clone();
            env.test_const_mut(&name("KR1N.mk")).expect("KR1N.mk").type_ = forged.clone();
            env
        };
        let k = ReferenceKernel::new(forge()).expect("stamp kept");
        expect_family_recheck(
            cite(&k, "KR1N.mk"),
            &["KR1N", "KR1N.mk"],
            "refused by the kernel",
        );

        let mut env = forge();
        env.test_inductive_mut(&name("KR1N"))
            .expect("KR1N")
            .all_names = vec![name("KR1U")];
        let k = ReferenceKernel::new(env).expect("stamp kept");
        for cited in ["KR1N.mk", "KR1N"] {
            expect_family_recheck(
                cite(&k, cited),
                &["KR1N", "KR1N.mk", "KR1N.rec"],
                "does not generate",
            );
        }

        let mut env = forge();
        env.test_constructor_mut(&name("KR1N.mk"))
            .expect("KR1N.mk")
            .inductive_name = name("KR1U");
        let k = ReferenceKernel::new(env).expect("stamp kept");
        let r = cite(&k, "KR1N.mk");
        assert!(
            matches!(&r, Err(ReferenceRefusal::BaseRecheck { .. })),
            "a constructor redirected to another block refuses: {r:?}"
        );
    }

    /// R161 (review probe B): an orphan record (stamped, of a family, but
    /// in none of the family's lists) is refused. Over `KR1F : Prop` and
    /// `KR1E : Type`, both empty, a stamped constructor record `KR1E.mk :
    /// KR1E` copied from `KR1U.u` would prove the empty `KR1F` as
    /// `KR1E.rec (fun _ => KR1F) KR1E.mk`; a stamped recursor record
    /// `KR1E.elim` copied from `KR1U.rec` (a name no block's recursor takes)
    /// is refused the same way. Mutant: the membership check removed accepts
    /// the proof of `KR1F` as `Ok(LeanReferenceV1)`. Control: the honest
    /// members `KR1U.u`, `KR1U.rec` and `KR1E.rec` are accepted, and the
    /// same motive applied to `KR1U.u` through `KR1U.rec` is not a proof of
    /// anything but the kernel's own refusal of a mistyped term.
    #[test]
    fn test_recheck_refuses_an_orphan_constructor_or_recursor() {
        let base = || {
            let mut env = Environment::default();
            add_family(&mut env, "KR1F", Expr::prop(), &[]);
            add_family(&mut env, "KR1E", Expr::type_(), &[]);
            add_family(
                &mut env,
                "KR1U",
                Expr::type_(),
                &[("KR1U.u", Expr::const_(name("KR1U"), vec![]))],
            );
            env
        };
        let k = ReferenceKernel::new(base()).expect("honest base");
        for honest in ["KR1U.u", "KR1U.rec", "KR1E.rec"] {
            cite(&k, honest).unwrap_or_else(|e| panic!("control {honest}: {e:?}"));
        }

        let e = || Expr::const_(name("KR1E"), vec![]);
        let mut env = base();
        env.test_clone_member(&name("KR1U.u"), &name("KR1E.mk"));
        {
            let c = env.test_constructor_mut(&name("KR1E.mk")).expect("KR1E.mk");
            c.type_ = e();
            c.inductive_name = name("KR1E");
        }
        env.test_const_mut(&name("KR1E.mk")).expect("KR1E.mk").type_ = e();
        let k = ReferenceKernel::new(env).expect("stamp kept");
        expect_family_recheck(cite(&k, "KR1E.mk"), &["KR1E.mk"], "does not generate");
        let rec_levels = k
            .environment()
            .get_const(&name("KR1E.rec"))
            .expect("KR1E.rec")
            .level_params
            .len();
        let motive = Expr::lam(BinderInfo::Default, e(), Expr::const_(name("KR1F"), vec![]));
        let proof = Expr::app(
            Expr::app(
                Expr::const_(name("KR1E.rec"), vec![Level::zero(); rec_levels]),
                motive,
            ),
            Expr::const_(name("KR1E.mk"), vec![]),
        );
        let r = k.check_closed_term(&Expr::const_(name("KR1F"), vec![]), &proof);
        assert!(
            matches!(&r, Err(ReferenceRefusal::BaseRecheck { .. })),
            "a proof of the empty KR1F through an orphan constructor refuses: {r:?}"
        );

        let mut env = base();
        env.test_clone_member(&name("KR1U.rec"), &name("KR1E.elim"));
        env.test_recursor_mut(&name("KR1E.elim"))
            .expect("KR1E.elim")
            .inductive_name = name("KR1E");
        let k = ReferenceKernel::new(env).expect("stamp kept");
        expect_family_recheck(cite(&k, "KR1E.elim"), &["KR1E.elim"], "does not generate");
    }

    /// Positive control over the real prelude (R161): every inductive block
    /// `Environment::with_prelude` holds (114 at this writing) re-admits
    /// through the kernel in the entry's theory and mode and matches its
    /// resident records, and genuine families cited through the entry are
    /// accepted. Mutant: the reference comparison made exact
    /// (`alpha_levels: false`) refuses `Eq`, whose prelude recursor is the
    /// hand-repaired `Eq.rec.{v, u}` with placeholder binder domains.
    #[test]
    fn test_recheck_readmits_with_prelude_families() {
        let k = ReferenceKernel::new(Environment::with_prelude()).expect("with_prelude");
        let env = k.environment();
        let mut heads: Vec<Name> = env
            .inductives()
            .filter_map(|i| i.all_names.first().cloned())
            .collect();
        heads.sort_by_cached_key(Name::to_string);
        heads.dedup();
        assert!(
            heads.len() > 100,
            "with_prelude holds {} blocks",
            heads.len()
        );
        let failing: Vec<String> = heads
            .iter()
            .filter_map(|h| {
                env.reference_recheck_inductive_block(h)
                    .err()
                    .map(|e| format!("{h}: {e}"))
            })
            .collect();
        assert!(
            failing.is_empty(),
            "blocks that do not re-admit: {failing:#?}"
        );
        // Every resident family record is a member its block generates.
        let members: Vec<Name> = env
            .inductives()
            .map(|i| i.name.clone())
            .chain(env.constructors().map(|c| c.name.clone()))
            .chain(env.recursors().map(|r| r.name.clone()))
            .collect();
        let orphans: Vec<String> = members
            .iter()
            .filter_map(|m| k.recheck_family_block(m).err().map(|e| format!("{m}: {e}")))
            .collect();
        assert!(
            orphans.is_empty(),
            "records no block generates: {orphans:#?}"
        );
        for n in [
            "Nat.succ",
            "Nat.rec",
            "List.cons",
            "Eq.refl",
            "Eq.rec",
            "And.intro",
            "Prod.mk",
            "Or.inl",
        ] {
            assert!(env.get_const(&name(n)).is_some(), "{n} in with_prelude");
            cite(&k, n).unwrap_or_else(|e| panic!("{n}: {e:?}"));
        }
    }

    /// The pin: the digest of the LIVE `Nat` list plus the string tag is the
    /// constant `LeanReferenceV1` carries. Changing either without bumping
    /// `TheoryId` fails here.
    #[test]
    fn test_lean_reference_v1_digest_is_pinned_to_the_live_inputs() {
        let live = theory_digest(&LEAN_KERNEL_NAT_EXTENSIONS, &[STRING_LITERAL_EXPANSION_TAG]);
        assert_eq!(
            live,
            TheoryId::LeanReferenceV1.digest(),
            "live digest {live:02x?}"
        );
    }
}

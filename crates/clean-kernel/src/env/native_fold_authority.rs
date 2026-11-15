// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native-fold AUTHORITY: a name-keyed reduction fires only for a constant
//! whose environment entry is a definition the fold is justified by.
//!
//! The kernel computes some constants natively instead of unfolding them:
//! `reduce_nat` folds `Nat.add`/`Nat.gcd`/… on literals, `reduce_int` folds
//! `Int.add`/`Int.sub`/`Int.mul`, `Lean.reduceBool`/`Lean.reduceNat` evaluate
//! their argument, string literals expand through `String.ofList`/`Char.ofNat`,
//! and ~200 registered native reducers (`native_reducers_*.rs`) compute their
//! head. Every one of those rules was keyed on the constant's NAME alone, and
//! the environment lets a user declare any name it does not already hold.
//! Lean's C++ kernel has the same shape (`type_checker::reduce_nat`,
//! v4.30.0-rc2 and v4.33.1 alike, compares `f == *g_nat_gcd` and nothing
//! else). Measured 2026-09-26 (Crystal E4c, `docs/issues/2026-09-26-kernel-
//! native-fold-by-name.md`): on `with_prelude`, which does not declare
//! `Nat.gcd`, `Nat.gcd := fun _ _ => 0` plus the fold gave `2 = 0` and then
//! `False` with an empty domain-axiom closure; and `Nat.shiftRight`, a
//! value-less AXIOM there, computed `8 >>> 1 = 4` by `rfl`.
//!
//! A fold is justified exactly when the constant's own δ-unfolding computes
//! what the fold computes. This module decides that by CONTENT, never by name
//! or provenance: it digests the constant's δ-closure and admits the fold only
//! when the digest is one the kernel holds as canonical
//! ([`super::native_fold_canon`]): Clean's own prelude definitions and Lean
//! `Init`'s definitions as imported from `.olean`, per supported toolchain.
//! Anything else — an absent constant, an axiom, a theorem, an opaque, a
//! definition whose closure differs anywhere — does not fold; it δ-unfolds as
//! an ordinary definition or stays stuck. Against Clean's own semantics that
//! is sound: a fold never fires that the definition does not justify. Against
//! LEAN's verdict it is not monotone: Lean's kernel folds these names
//! whatever their declaration says, so for a forged `Nat.add := fun a _ => a`
//! Lean computes `2 + 3 = 5` and refuses `Nat.add 2 3 = 2`, while Clean
//! unfolds the forgery and admits it. A front door that reports Lean's verdict
//! must therefore decline an environment that declares such a name without
//! this authority: the NDJSON door does (decision R128). The `.olean` door's
//! analogue, a forged `Init` module that redefines a fold head, is open
//! (R128).
//!
//! A pinned digest carries a [`FoldRole`]. Only a `fold` row lets the name's
//! OWN rules fire — its registered reducer, its `reduce_nat`/`reduce_int`
//! fold, the string-literal expansion — because only then has the fold been
//! reviewed against that exact closure (`native_fold_review.rs`). A
//! `definition` row vouches only that the closure is known: it may be a
//! BOUNDARY of a reviewed closure or a constant a reviewed reducer reads in its
//! arguments (measured 2026-09-28: Lean 4.30's `String.drop` returns a
//! `String.Slice`, Clean's reducer a `String`, and pinning the digest turned
//! the reducer on, so `String.drop "abc" 1 = String.drop "xbc" 1` checked by
//! `rfl`).
//!
//! # The digest
//!
//! A Merkle digest (SHA-256) over the constant's δ-closure, walked from its
//! VALUE (types are hashed, never walked: they do not compute). Each member
//! contributes a record by kind — definition (type + value), opaque (type +
//! value), axiom (type), theorem (kind only: a proof's content cannot change a
//! computed value), inductive / constructor / recursor (their registry shape,
//! recursor rules included, since ι computes with them), quotient primitive
//! (its kind). `MData` and binder annotations are transparent, as they are to
//! reduction. A member that is itself a fold key (the [`fold_key_universe`]) is
//! a BOUNDARY: it contributes its name and must be authorized in turn, so a
//! canonical `Nat.mul` over a user's `Nat.add` is refused, while Clean's and
//! Lean's definitions of two different fold keys may meet at a boundary (each
//! is pinned to its own specification). A cycle, an absent member, a
//! value-less non-inductive definition, a free variable, a metavariable, or a
//! Clean-only expression form refuses.
//!
//! # Cost
//!
//! Nothing is computed at registration. A verdict is computed on first use,
//! cached per environment (keyed by `generation` and constant count, the key
//! the type checker's own caches use), and memoized per checker, so a fold
//! pays one hash-map lookup after its first use.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::{LazyLock, Mutex};

use sha2::{Digest as _, Sha256};

use super::native_fold_canon::canonical_digests;
pub use super::native_fold_canon::FoldRole;
use super::native_fold_digest::{put_str, strip_binders_eq, ExprHasher, MemberError, MemberMemo};
use super::types::ConstantKind;
use super::Environment;
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

/// Most closure members walked for one fold key before refusing (fail-closed).
const FOLD_CLOSURE_CAP: usize = 20_000;

/// Domain separator for every digest this module mints. Bump it (and re-pin
/// [`super::native_fold_canon`]) if the record format below changes.
const DIGEST_DOMAIN: &[u8] = b"clean-native-fold-authority-v1";

/// Constants the kernel folds by name outside the native-reducer registry:
/// `reduce_nat` (the fourteen binary heads Lean's `reduce_nat` has, plus
/// Clean's `Nat.pred`), `reduce_int`, the `Lean.reduceBool`/`Lean.reduceNat`
/// extensions, and the two definitions a string literal expands through.
pub(crate) const NATIVE_FOLD_KEYS: &[&str] = &[
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.gcd",
    "Nat.pow",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "Nat.pred",
    "Int.add",
    "Int.sub",
    "Int.mul",
    "Lean.reduceBool",
    "Lean.reduceNat",
    "Char.ofNat",
    "String.ofList",
];

/// Fold keys whose canonical entry is an `opaque` whose stored value states
/// the rule (`opaque Lean.reduceBool (b : Bool) : Bool := b`). Every other
/// key must be a value-carrying definition.
const OPAQUE_FOLD_KEYS: &[&str] = &["Lean.reduceBool", "Lean.reduceNat"];

/// Every name some name-keyed kernel rule may fire on: [`NATIVE_FOLD_KEYS`],
/// every head any native-reducer registration installs, and every
/// non-constructor constant a reducer recognizes in its arguments
/// ([`super::native_fold_canon::RECOGNIZED_ARGUMENT_NAMES`]). Derived from the
/// registration functions (a scratch environment runs them), so it cannot drift
/// from what `ensure_native_reducers` installs. Static, so a digest does not
/// depend on which reducers one environment happens to hold.
pub(crate) fn fold_key_universe() -> &'static HashSet<Name> {
    static UNIVERSE: LazyLock<HashSet<Name>> = LazyLock::new(|| {
        let mut scratch = Environment::default();
        scratch.ensure_native_reducers();
        let mut names: HashSet<Name> = scratch.registered_native_reducer_names().cloned().collect();
        names.extend(NATIVE_FOLD_KEYS.iter().map(|s| Name::from_string(s)));
        names.extend(
            super::native_fold_canon::RECOGNIZED_ARGUMENT_NAMES
                .iter()
                .map(|s| Name::from_string(s)),
        );
        names
    });
    &UNIVERSE
}

/// A 32-byte closure digest.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FoldDigest(pub [u8; 32]);

impl FoldDigest {
    /// Lower-case hex, the spelling [`super::native_fold_canon`] pins.
    #[must_use]
    pub fn to_hex(&self) -> String {
        use std::fmt::Write as _;
        let mut out = String::with_capacity(64);
        for byte in self.0 {
            let _ = write!(out, "{byte:02x}");
        }
        out
    }
}

impl std::fmt::Debug for FoldDigest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_hex())
    }
}

/// Why a name-keyed fold is refused.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum FoldRefusal {
    /// The environment does not hold this constant.
    Absent(Name),
    /// The fold key is not a value-carrying definition (an axiom, a theorem, a
    /// constructor, an opaque where a definition is required, …).
    HeadNotDefinition(Name),
    /// A closure member is a value-less definition outside the inductive and
    /// quotient registries, so its computation cannot be seen.
    NoValue(Name),
    /// A closure member holds an expression form a canonical definition never
    /// contains (a free variable, a metavariable, a Clean-only form).
    UnsupportedExpr(Name),
    /// The closure exceeds [`FOLD_CLOSURE_CAP`] members.
    ClosureTooLarge,
    /// A boundary fold key reached itself.
    Cycle(Name),
    /// A boundary fold key the closure depends on is refused.
    Boundary {
        /// The boundary key.
        key: Name,
        /// Why it is refused.
        cause: Box<FoldRefusal>,
    },
    /// The closure is well formed but its digest is not a canonical one.
    NotCanonical {
        /// The digest the environment's closure has.
        digest: FoldDigest,
    },
    /// `Nat` is not the canonical two-constructor inductive, so no literal
    /// extension is meaningful.
    NatNotCanonical,
    /// The closure is a known definition (a `definition` row of this world),
    /// but the name's own rules were not reviewed against it, or disagree
    /// with it, so they do not fire.
    NotReviewed {
        /// The world whose `definition` row the closure matched.
        world: FoldWorld,
    },
    /// The closure is a known definition, but a review measured the name's
    /// own rules DISAGREEING with it (a `refused` row), so they do not fire.
    ReviewRefused {
        /// The world whose `refused` row the closure matched.
        world: FoldWorld,
    },
}

/// Which canonical world a fold key's closure matched.
pub type FoldWorld = &'static str;

/// The FOLD verdict: the world whose `fold` row admits the name's own rules,
/// or why they may not fire.
pub type FoldVerdict = Result<FoldWorld, FoldRefusal>;

/// The DEFINITION verdict: the world and role of the row the closure matched
/// (any role), or why the closure is not a known definition.
pub type DefinitionVerdict = Result<(FoldWorld, FoldRole), FoldRefusal>;

/// Per-environment verdict cache. Not serialized and not cloned: a verdict is a
/// function of the environment's content, so a clone or a deserialized
/// environment recomputes it.
#[derive(Default)]
pub struct NativeFoldAuthorityCache {
    inner: Mutex<CacheInner>,
}

#[derive(Default)]
struct CacheInner {
    key: (u64, usize),
    verdicts: HashMap<Name, DefinitionVerdict>,
    nat_canonical: Option<bool>,
    /// Member records, keyed by name and validated by snapshot on every use
    /// (`native_fold_digest.rs`), so they survive the verdicts' invalidation:
    /// a closure whose members did not change costs pointer compares, not a
    /// re-hash, after the environment grows.
    members: HashMap<Name, MemberMemo>,
}

impl Clone for NativeFoldAuthorityCache {
    fn clone(&self) -> Self {
        Self::default()
    }
}

impl std::fmt::Debug for NativeFoldAuthorityCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("NativeFoldAuthorityCache")
    }
}

/// The digest of a fold key's closure and the boundary keys it rests on.
#[derive(Debug, Clone)]
pub struct FoldClosure {
    /// The Merkle digest of the closure.
    pub digest: FoldDigest,
    /// Boundary fold keys the closure mentions (each must be authorized).
    pub boundaries: Vec<Name>,
    /// Members digested (the head included).
    pub members: usize,
    /// Axioms the closure reaches (the pin batteries refuse to pin a closure
    /// whose computation rests on a non-proof axiom).
    pub axioms: Vec<Name>,
}

impl Environment {
    /// Whether the name-keyed rules of `name` (its reducer, its kernel fold)
    /// may fire in this environment: a `fold` row matches its closure.
    #[must_use]
    pub fn native_fold_authorized(&self, name: &Name) -> bool {
        self.native_fold_verdict(name).is_ok()
    }

    /// The fold verdict for `name`: the world whose `fold` row its closure
    /// matched, or why its rules are refused (`NotReviewed` when only a
    /// `definition` row matches).
    pub fn native_fold_verdict(&self, name: &Name) -> FoldVerdict {
        match self.native_fold_definition_verdict(name)? {
            (world, FoldRole::Fold) => Ok(world),
            (world, FoldRole::Definition) => Err(FoldRefusal::NotReviewed { world }),
            (world, FoldRole::Refused) => Err(FoldRefusal::ReviewRefused { world }),
        }
    }

    /// Whether `name`'s closure is a known definition (a row of any role
    /// matches it): enough for it to be a boundary of a reviewed closure, or a
    /// constant a reviewed reducer reads in its arguments.
    #[must_use]
    pub fn native_fold_definition_admitted(&self, name: &Name) -> bool {
        self.native_fold_definition_verdict(name).is_ok()
    }

    /// The definition verdict for `name`: the world and role of the row its
    /// closure matched, or why it is not a known definition.
    pub fn native_fold_definition_verdict(&self, name: &Name) -> DefinitionVerdict {
        #[cfg(any(test, feature = "test-fixtures"))]
        if mint_bypass::active() {
            return Ok(("mint-bypass", FoldRole::Fold));
        }
        let mut inner = self.lock_fold_cache();
        let mut in_progress = HashSet::new();
        self.fold_verdict_in(name, &mut inner, &mut in_progress)
    }

    /// Whether `Nat` is the canonical inductive every literal extension assumes:
    /// no parameters or indices, `Nat : Type`, constructors exactly
    /// `Nat.zero : Nat` and `Nat.succ : Nat → Nat` in that order.
    #[must_use]
    pub fn nat_literal_extension_canonical(&self) -> bool {
        #[cfg(any(test, feature = "test-fixtures"))]
        if mint_bypass::active() {
            return true;
        }
        let mut inner = self.lock_fold_cache();
        if let Some(known) = inner.nat_canonical {
            return known;
        }
        let verdict = self.compute_nat_canonical();
        inner.nat_canonical = Some(verdict);
        verdict
    }

    fn lock_fold_cache(&self) -> std::sync::MutexGuard<'_, CacheInner> {
        let key = (self.generation(), self.num_constants());
        let mut inner = self
            .native_fold_cache
            .inner
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if inner.key != key {
            inner.key = key;
            inner.verdicts.clear();
            inner.nat_canonical = None;
        }
        inner
    }

    fn fold_verdict_in(
        &self,
        name: &Name,
        inner: &mut CacheInner,
        in_progress: &mut HashSet<Name>,
    ) -> DefinitionVerdict {
        if let Some(known) = inner.verdicts.get(name) {
            return known.clone();
        }
        if !in_progress.insert(name.clone()) {
            return Err(FoldRefusal::Cycle(name.clone()));
        }
        let verdict = self.compute_fold_verdict(name, inner, in_progress);
        in_progress.remove(name);
        inner.verdicts.insert(name.clone(), verdict.clone());
        verdict
    }

    fn compute_fold_verdict(
        &self,
        name: &Name,
        inner: &mut CacheInner,
        in_progress: &mut HashSet<Name>,
    ) -> DefinitionVerdict {
        let Some(head) = self.get_const(name) else {
            return Err(FoldRefusal::Absent(name.clone()));
        };
        let opaque_ok = OPAQUE_FOLD_KEYS.iter().any(|k| name.to_string() == *k);
        let head_ok = match head.kind {
            ConstantKind::Definition => head.value.is_some() && !self.is_inductive_family(name),
            ConstantKind::Opaque => opaque_ok,
            ConstantKind::Theorem | ConstantKind::Axiom => false,
        };
        if !head_ok {
            return Err(FoldRefusal::HeadNotDefinition(name.clone()));
        }
        if opaque_ok {
            // `Lean.reduceBool c ≡ c` (and `reduceNat`) is justified by exactly
            // one fact, checked structurally rather than by digest: the entry's
            // value IS the identity `fun (b : X) => b` at type `X → X`. Then
            // the rule is the entry's own δβ-reduction (the value Lean's
            // `opaque Lean.reduceBool (b : Bool) : Bool := b` states), whatever
            // world the entry came from.
            return if is_identity_function(&head.type_, head.value.as_ref()) {
                Ok(("identity", FoldRole::Fold))
            } else {
                Err(FoldRefusal::NotCanonical {
                    digest: FoldDigest([0; 32]),
                })
            };
        }
        let closure = self.fold_closure_with(name, &mut inner.members)?;
        // A boundary needs only to be a KNOWN definition: this closure's own
        // review saw it as the definition it is, whatever its own role.
        for key in &closure.boundaries {
            if let Err(cause) = self.fold_verdict_in(key, inner, in_progress) {
                return Err(FoldRefusal::Boundary {
                    key: key.clone(),
                    cause: Box::new(cause),
                });
            }
        }
        // The first matching row in file order, a `refused` row outranking a
        // `fold` row (a veto: `native_fold_canon::FoldRole::Refused`), a `fold`
        // row outranking a `definition` row. The table pins no digest both
        // `fold` and `refused` (`native_fold_canon_tests::
        // test_no_digest_is_pinned_fold_and_refused`).
        let rank = |role: FoldRole| match role {
            FoldRole::Definition => 0,
            FoldRole::Fold => 1,
            FoldRole::Refused => 2,
        };
        let mut matched: Option<(FoldWorld, FoldRole)> = None;
        for (world, digest, role) in canonical_digests().get(name).into_iter().flatten() {
            if *digest != closure.digest {
                continue;
            }
            if matched.is_none_or(|(_, seen)| rank(*role) > rank(seen)) {
                matched = Some((*world, *role));
            }
        }
        matched.ok_or(FoldRefusal::NotCanonical {
            digest: closure.digest,
        })
    }

    /// Digest `name`'s δ-closure (module docs). Public so the pin batteries can
    /// mint and re-derive [`super::native_fold_canon`].
    pub fn native_fold_closure(&self, name: &Name) -> Result<FoldClosure, FoldRefusal> {
        self.fold_closure_with(name, &mut HashMap::new())
    }

    fn fold_closure_with(
        &self,
        name: &Name,
        members: &mut HashMap<Name, MemberMemo>,
    ) -> Result<FoldClosure, FoldRefusal> {
        let universe = fold_key_universe();
        let mut hasher = ExprHasher::default();
        let mut records: BTreeMap<String, [u8; 32]> = BTreeMap::new();
        let mut boundaries: BTreeSet<Name> = BTreeSet::new();
        let mut axioms: BTreeSet<Name> = BTreeSet::new();
        let mut visited: HashSet<Name> = HashSet::from([name.clone()]);
        let mut stack: Vec<Name> = vec![name.clone()];
        while let Some(member) = stack.pop() {
            if visited.len() > FOLD_CLOSURE_CAP {
                return Err(FoldRefusal::ClosureTooLarge);
            }
            if member != *name && universe.contains(&member) && !self.is_inductive_family(&member) {
                boundaries.insert(member);
                continue;
            }
            let refusal = |e: MemberError| match e {
                MemberError::Absent => FoldRefusal::Absent(member.clone()),
                MemberError::NoValue => FoldRefusal::NoValue(member.clone()),
                MemberError::Unsupported => FoldRefusal::UnsupportedExpr(member.clone()),
            };
            let snapshot = self.fold_member_snapshot(&member).map_err(refusal)?;
            let fresh = !matches!(members.get(&member), Some(m) if m.snapshot == snapshot);
            if fresh {
                let memo = snapshot.memo(&member, &mut hasher).map_err(refusal)?;
                members.insert(member.clone(), memo);
            }
            let Some(memo) = members.get(&member) else {
                return Err(FoldRefusal::Absent(member));
            };
            if memo.axiom {
                axioms.insert(member.clone());
            }
            records.insert(memo.spelled.clone(), memo.record);
            for n in &memo.next {
                if visited.insert(n.clone()) {
                    stack.push(n.clone());
                }
            }
        }
        let mut out = Sha256::new();
        out.update(DIGEST_DOMAIN);
        put_str(&mut out, &name.to_string());
        for (member, record) in &records {
            put_str(&mut out, member);
            out.update(record);
        }
        out.update(b"boundaries");
        for key in &boundaries {
            put_str(&mut out, &key.to_string());
        }
        Ok(FoldClosure {
            digest: FoldDigest(out.finalize().into()),
            boundaries: boundaries.into_iter().collect(),
            members: records.len(),
            axioms: axioms.into_iter().collect(),
        })
    }

    /// The rows a pin battery mints for `world`: every fold key this
    /// environment holds as a value-carrying definition (or an allowed opaque)
    /// whose closure is well formed and rests on no axiom but `propext` and
    /// `Quot.sound` (proof axioms: they cannot change a computed value). Sorted
    /// by name. A name this environment cannot justify gets no row, so it
    /// cannot fold here.
    #[must_use]
    pub fn native_fold_pin_rows(&self) -> Vec<(Name, FoldDigest)> {
        const PROOF_AXIOMS: [&str; 2] = ["propext", "Quot.sound"];
        let mut names: Vec<&Name> = fold_key_universe().iter().collect();
        names.sort_by_cached_key(|n| n.to_string());
        let mut rows = Vec::new();
        let mut members = HashMap::new();
        for name in names {
            let Some(head) = self.get_const(name) else {
                continue;
            };
            // The identity keys are judged structurally, never pinned.
            if OPAQUE_FOLD_KEYS.iter().any(|k| name.to_string() == *k) {
                continue;
            }
            let head_ok = match head.kind {
                ConstantKind::Definition => head.value.is_some() && !self.is_inductive_family(name),
                ConstantKind::Opaque | ConstantKind::Theorem | ConstantKind::Axiom => false,
            };
            if !head_ok {
                continue;
            }
            let Ok(closure) = self.fold_closure_with(name, &mut members) else {
                continue;
            };
            // A proof axiom is the kernel's canonical declaration of one of
            // these names, compared structurally — never by printed form (a
            // user `axiom «propext» : …` prints `propext`).
            if closure.axioms.iter().any(|a| {
                !(self.is_canonical_foundational_axiom(a)
                    && PROOF_AXIOMS
                        .iter()
                        .any(|p| super::axiom_audit::name_has_components(a, p)))
            }) {
                continue;
            }
            rows.push((name.clone(), closure.digest));
        }
        rows
    }

    fn is_inductive_family(&self, name: &Name) -> bool {
        self.get_inductive(name).is_some()
            || self.get_constructor(name).is_some()
            || self.get_recursor(name).is_some()
            || self.get_quot(name).is_some()
    }

    fn compute_nat_canonical(&self) -> bool {
        let nat = Name::from_string("Nat");
        let zero = Name::from_string("Nat.zero");
        let succ = Name::from_string("Nat.succ");
        let nat_const = Expr::const_(nat.clone(), vec![]);
        let Some(ind) = self.get_inductive(&nat) else {
            return false;
        };
        let shape = ind.level_params.is_empty()
            && ind.num_params == 0
            && ind.num_indices == 0
            && ind.constructor_names == [zero.clone(), succ.clone()]
            && ind.type_ == Expr::sort(Level::succ(Level::zero()));
        let ctor_ok = |c: &Name, idx: u32, fields: u32, ty: &Expr| {
            self.get_constructor(c).is_some_and(|cv| {
                cv.inductive_name == nat
                    && cv.level_params.is_empty()
                    && cv.num_params == 0
                    && cv.num_fields == fields
                    && cv.constructor_idx == idx
                    && strip_binders_eq(&cv.type_, ty)
            })
        };
        let succ_ty = Expr::pi(
            crate::expr::BinderInfo::Default,
            nat_const.clone(),
            nat_const.clone(),
        );
        shape && ctor_ok(&zero, 0, 0, &nat_const) && ctor_ok(&succ, 1, 1, &succ_ty)
    }
}

/// `ty = (b : X) → X` (non-dependent) and `value = fun (_ : X) => #0`, up to
/// binder annotations and `MData`.
fn is_identity_function(ty: &Expr, value: Option<&Expr>) -> bool {
    use crate::expr::ExprKind;
    let Some(value) = value else {
        return false;
    };
    let (ExprKind::Pi(_, dom, cod), ExprKind::Lam(_, arg, body)) =
        (ty.strip_mdata().kind(), value.strip_mdata().kind())
    else {
        return false;
    };
    // The codomain is the domain, not lifted over the binder (no loose bvar).
    cod.loose_bvar_range() == 0
        && strip_binders_eq(dom, cod)
        && strip_binders_eq(dom, arg)
        && matches!(body.strip_mdata().kind(), ExprKind::BVar(0))
}

/// BOOTSTRAP for the pin batteries, compiled only into test builds (this
/// crate's unit tests, and downstream test builds through the `test-fixtures`
/// feature their `[dev-dependencies]` enable — the R1-TESTDOOR pattern, so no
/// production build can call it): while active, every fold is admitted by
/// name, which is exactly the pre-authority kernel. The batteries raise it ONLY
/// under `CLEAN_NATIVE_FOLD_REPIN=1`, to build a world the way it was built
/// before any pin existed and digest what it holds; the ordinary run of the
/// same battery builds it under authority and must reproduce the pins.
/// Process-global: isolate bootstrap callers from tests that require normal authority.
/// Nested and overlapping scopes keep it active until the last scope exits,
/// including when a closure unwinds.
#[cfg(any(test, feature = "test-fixtures"))]
pub mod mint_bypass {
    use std::sync::atomic::{AtomicUsize, Ordering};

    static ACTIVE: AtomicUsize = AtomicUsize::new(0);

    struct Scope;

    impl Drop for Scope {
        fn drop(&mut self) {
            let _previous = ACTIVE.fetch_sub(1, Ordering::SeqCst);
        }
    }

    /// Whether the bootstrap is active.
    pub(crate) fn active() -> bool {
        ACTIVE.load(Ordering::SeqCst) != 0
    }

    /// Run `f` with every fold admitted by name (see the module docs).
    pub fn run<R>(f: impl FnOnce() -> R) -> R {
        ACTIVE
            .try_update(Ordering::SeqCst, Ordering::SeqCst, |active| {
                active.checked_add(1)
            })
            .expect("native-fold bootstrap scope count overflow");
        let _scope = Scope;
        f()
    }
}

#[cfg(test)]
#[path = "native_fold_authority_tests.rs"]
mod tests;

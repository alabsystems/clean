// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binding the kernel's BY-NAME reductions to the declarations they assume.
//!
//! # What was wrong
//!
//! Some kernel reductions fire on a constant's NAME, never consulting the
//! declaration that carries it: `Nat.add 2 2` is evaluated with bignum
//! arithmetic (`tc/reduction/nat.rs`), `Int.mul` likewise
//! (`tc/reduction/int.rs`), a string literal is expanded into
//! `String.ofList (List.cons (Char.ofNat …) …)`, and — until 2026-09-24 in this
//! lane — some 20 families of Clean's own host-evaluation reducers
//! (`env/native_reducers*.rs`: `Bool.not`, `Decidable.decide`, `UInt*`,
//! `String`, `Float`, `BitVec`, …) were installed in the replay environment and
//! consulted by name at `tc/def_eq/delta_helpers.rs`.
//!
//! The dependency-closed replay re-admits every declaration in the cone through
//! `add_decl`. So an imported cone that supplies its OWN declaration for one of
//! those names gives the constant two meanings — the forged one by δ, the
//! built-in one by name — and each step of a proof that plays one against the
//! other is well-typed under a kernel that believes both. The verifier's attack
//! (round 22): `Bool.not := fun b => b` plus `∀ b, Bool.not b = b := rfl` gives
//! a closed `RC.False` that the replay PASSED.
//!
//! # What this does
//!
//! Two things, one per kind of by-name reduction.
//!
//! 1. **Clean's native-reducer table is not installed.** It is an accelerator
//!    set with no counterpart in Lean's kernel, so no Lean-checked declaration
//!    needs it to type-check; none of its entries is tied to a definition. The
//!    replay environment starts with an empty table and nothing adds to it.
//! 2. **The kernel's built-in by-name reductions are GATED.** Every name in
//!    [`EXTENSION_KEYS`] — the names `tc/` matches on in the replay's mode — is
//!    admitted only if its declaration's *dependency-closed fingerprint*
//!    matches the one pinned for it in [`ExtensionBindings::pinned`]. The
//!    fingerprint is a Merkle hash over the declaration and, recursively, every
//!    constant its type or value mentions, so a forgery one constant deeper
//!    (`Nat.add := fun a b => helper a b` with `helper` forged) changes it too.
//!    A mismatch refuses the name (`ExtensionBindingMismatch`), and everything
//!    that depends on it is refused in turn.
//!
//! [`every_by_name_hook_in_the_type_checker_is_gated_or_explained`] scans
//! `clean-kernel/src/tc` for by-name matches and fails on any name that is
//! neither gated here nor listed in [`INERT_IN_REPLAY`] with the reason it
//! cannot fire in the replay environment.
//!
//! # Round 24: names the kernel BUILDS or STRIPS by name, anywhere in the crate
//!
//! The `tc/` scan missed by-name references outside `tc/` and in other
//! spellings, and one of them was a false accept: `quot.rs` builds the types
//! of `Quot.lift` and `Quot.sound` around the constant NAMED `Eq`, the replay
//! installed the quotient before admitting the cone, and the cone's own `Eq`
//! (`Eq a b := False`, or an `Eq` with no constructor) then gave the counted
//! axiom `Quot.sound` a false statement. Three changes:
//!
//! * the quotient is installed lazily, only through
//!   `Environment::add_quot` — Lean's `add_quot` precondition that the
//!   already-admitted `Eq` is an inductive with exactly the shape those types
//!   assume — and no cone declaration is ever admitted under a quotient name
//!   (`drive::provide_quotient`);
//! * `Eq`, and the four annotation names `inductive/mod.rs`
//!   `consume_type_annotations` strips by name when it generates a recursor
//!   (`optParam`, `autoParam`, `outParam`, `semiOutParam`), are extension keys
//!   pinned like the rest;
//! * `by_name_census_tests` enumerates, over the WHOLE kernel crate, every
//!   identifier-shaped string literal in code the replay can reach (an
//!   over-approximation checked against the linker by
//!   `scripts/replay_reachability_census.sh`), and fails on any that is not an
//!   extension key, a quotient primitive, or explained per source file.
//!
//! # What the pinned table is
//!
//! The union of the reviewed WORLDS in `extension_binding_pins.rs`: the
//! fingerprints the core declarations of those names produce when a Lean
//! release's `Init` is imported by this crate — Lean v4.8.0 (the release the
//! Trust semantics library is built against) and Lean v4.30.0-rc2 (the
//! workspace pin; decoded over an empty base, and over the import-mode prelude
//! `clean check --imports-prefer-olean` snapshots). A key is bound when its
//! fingerprint is ANY world's row for it. Each row asserts "the built-in
//! reduction for `N` is the one this world's `N` computes", which is the
//! kernel's trusted claim about that reduction; it does NOT make the reduction
//! itself checked. A cone built against a release no world pins is refused at
//! the first key it uses, fail-closed, until a world for that release is
//! reviewed and pinned.
//! A partial 4.35 world additionally qualifies character/string literals and
//! natural division/modulo, not every 4.35 primitive (see its retained report).
//!
//! # Round 29: a table for one Lean world refused the workspace pin's
//!
//! Until 2026-09-28 the only world was Lean v4.8.0, and every `.olean` the
//! source-elab corpus loads is Lean v4.30.0-rc2's, whose `Nat.add` (and every
//! other key's cone) fingerprints differently. So `clean check
//! --imports-prefer-olean` refused every citation whose cone reached a key —
//! `Mathlib/Order/Basic.lean` went from 151 credited declarations to 47, each
//! refusal naming `Nat.add` or `Nat.beq` as "not bound to this declaration".
//! The v4.30.0-rc2 worlds are measured and reviewed in
//! `reports/2026-09-28-extension-binding-v4-30.md`, which also records the
//! second refusal the same citations hit once this one was lifted (a v4.30
//! `BitVec.ofFin` refused for sharing a name with a native reducer; see
//! `drive.rs`).
//!
//! [`every_by_name_hook_in_the_type_checker_is_gated_or_explained`]:
//! tests::every_by_name_hook_in_the_type_checker_is_gated_or_explained

use super::extension_binding_pins::PINNED_WORLDS;
#[cfg(test)]
use super::fingerprint::Fingerprinter;
#[cfg(test)]
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use std::collections::BTreeMap;

/// A name some type-checker reduction matches by name in the replay's mode.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ExtensionKey {
    /// The constant's name.
    pub name: &'static str,
    /// Where the kernel matches it, and what it does with it.
    pub hook: &'static str,
}

const NAT_LIT: &str = "tc/reduction/nat.rs: literal typing, `Nat.succ`/`Nat.zero` literal \
                       expansion and offset def-eq assume this is Lean's `Nat`";
const NAT_OP: &str = "tc/reduction/nat.rs `reduce_nat`: evaluated on literals by bignum \
                      arithmetic, never by unfolding";
const INT_OP: &str = "tc/reduction/int.rs: `reduce_int` evaluates `Int.add/sub/mul` on big \
                      literals; `reduce_int_pred_fold` matches `Nat.rec`/`Int.rec` folds";
const STR_LIT: &str = "tc/reduction/nat.rs `string_lit_to_constructor`: a string literal \
                       expands to `String.ofList (List.cons (Char.ofNat k) …)`";

const EQ_BY_NAME: &str = "quot.rs `make_eq_type`: the KERNEL-BUILT types of `Quot.lift` and \
                          `Quot.sound` name `Eq` and are never re-derived (installed only by \
                          `Environment::add_quot`, after Lean's `check_eq_type`)";
const TYPE_ANNOTATION: &str = "inductive/mod.rs `consume_type_annotations`: \
                               `add_inductive_core` strips `optParam α d` / `autoParam α t` / \
                               `outParam α` / `semiOutParam α` to `α` BY NAME in every \
                               generated recursor's binder domains, which is sound only if \
                               each unfolds to `α`";

/// Every name the kernel reduces, builds or strips BY NAME in a way that CAN
/// matter in the replay environment (classical mode, no native reducers, no
/// monad-class prelude): the `tc/` reductions, `Eq` (the kernel-built quotient
/// types) and the four type annotations recursor generation strips.
pub(crate) const EXTENSION_KEYS: &[ExtensionKey] = &[
    ExtensionKey {
        name: "Nat",
        hook: NAT_LIT,
    },
    ExtensionKey {
        name: "Nat.zero",
        hook: NAT_LIT,
    },
    ExtensionKey {
        name: "Nat.succ",
        hook: NAT_LIT,
    },
    ExtensionKey {
        name: "Nat.rec",
        hook: INT_OP,
    },
    ExtensionKey {
        name: "Nat.pred",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.add",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.sub",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.mul",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.div",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.mod",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.gcd",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.pow",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.beq",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.ble",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.land",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.lor",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.xor",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.shiftLeft",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Nat.shiftRight",
        hook: NAT_OP,
    },
    ExtensionKey {
        name: "Int",
        hook: INT_OP,
    },
    ExtensionKey {
        name: "Int.ofNat",
        hook: INT_OP,
    },
    ExtensionKey {
        name: "Int.negSucc",
        hook: INT_OP,
    },
    ExtensionKey {
        name: "Int.rec",
        hook: INT_OP,
    },
    ExtensionKey {
        name: "Int.add",
        hook: INT_OP,
    },
    ExtensionKey {
        name: "Int.sub",
        hook: INT_OP,
    },
    ExtensionKey {
        name: "Int.mul",
        hook: INT_OP,
    },
    ExtensionKey {
        name: "Bool.true",
        hook: "tc/def_eq/delta_helpers.rs + reduction/mod.rs: `Lean.reduceBool` / `Nat.beq` \
               results are minted as these constructors",
    },
    ExtensionKey {
        name: "Bool.false",
        hook: "tc/def_eq/delta_helpers.rs + reduction/mod.rs: `Lean.reduceBool` / `Nat.beq` \
               results are minted as these constructors",
    },
    ExtensionKey {
        name: "String",
        hook: STR_LIT,
    },
    ExtensionKey {
        name: "String.ofList",
        hook: STR_LIT,
    },
    ExtensionKey {
        name: "List.nil",
        hook: STR_LIT,
    },
    ExtensionKey {
        name: "List.cons",
        hook: STR_LIT,
    },
    ExtensionKey {
        name: "Char",
        hook: STR_LIT,
    },
    ExtensionKey {
        name: "Char.ofNat",
        hook: STR_LIT,
    },
    ExtensionKey {
        name: "Lean.reduceBool",
        hook: "tc/def_eq/delta_helpers.rs: `Lean.reduceBool c` is evaluated by reducing `c`, \
               not by unfolding `Lean.reduceBool`",
    },
    ExtensionKey {
        name: "Lean.reduceNat",
        hook: "tc/def_eq/delta_helpers.rs: `Lean.reduceNat c` is evaluated by reducing `c`, \
               not by unfolding `Lean.reduceNat`",
    },
    ExtensionKey {
        name: "Eq",
        hook: EQ_BY_NAME,
    },
    ExtensionKey {
        name: "optParam",
        hook: TYPE_ANNOTATION,
    },
    ExtensionKey {
        name: "autoParam",
        hook: TYPE_ANNOTATION,
    },
    ExtensionKey {
        name: "outParam",
        hook: TYPE_ANNOTATION,
    },
    ExtensionKey {
        name: "semiOutParam",
        hook: TYPE_ANNOTATION,
    },
];

/// The legacy string expansion admits a representation, not a function body.
/// Its exact constructor/telescope checks are independent of name fingerprints.
#[cfg(test)]
pub(super) const LEGACY_STRING_LAYOUT: &str = "legacy string literal representation: `string_literal_admitted` requires canonical Nat/Char folds and either canonical String.ofList or its absence plus `list_backed_string_constructor_uncached`; the latter checks the complete String/List inductive and constructor metadata, universe/binder telescopes and bodyless constant types. A function named String.mk cannot pass. Every call to `expand_admitted_string_literal` is guarded by that admission; `string_literal_legacy` tests both honest constructor expansion and missing/forged conversion refusals";

/// Names `tc/` matches by name that cannot change a verdict in the replay
/// environment, each with the reason. Consumed by the source scan in the tests
/// (`every_by_name_hook_in_the_type_checker_is_gated_or_explained`), which is
/// what keeps this list and [`EXTENSION_KEYS`] exhaustive.
#[cfg(test)]
pub(crate) const INERT_IN_REPLAY: &[(&str, &str)] = &[
    ("String.mk", LEGACY_STRING_LAYOUT),
    (
        "<cubical-layer>",
        "a memo KEY of the checker's admission cache (tc/fold_admission.rs, the cubical layer's admission verdict), never looked up as a constant; `<…>` is not a name any declaration can carry",
    ),
    // Consulted only AFTER `get_native_reducer(name)?` succeeds
    // (tc/def_eq/delta_helpers.rs), and the replay installs no native reducer.
    (
        "decide",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "Decidable.decide",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "Nat.decEq",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "instDecidableEqNat",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "UInt8.decEq",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "UInt16.decEq",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "UInt32.decEq",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "UInt64.decEq",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "USize.decEq",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "UInt8.decLt",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "UInt16.decLt",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "UInt32.decLt",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "UInt64.decLt",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    (
        "USize.decLt",
        "native-reducer operand pre-WHNF; no native reducer is installed",
    ),
    // tc/def_eq/delta_helpers.rs: rebuilds `f (whnf arg)` with the SAME head;
    // the argument is replaced by its own kernel WHNF, nothing is evaluated by
    // name, so the term is def-eq to the original whatever `f` is.
    (
        "UInt8.ofNat",
        "argument normalisation only; the head is kept, no value is minted",
    ),
    (
        "UInt16.ofNat",
        "argument normalisation only; the head is kept, no value is minted",
    ),
    (
        "UInt32.ofNat",
        "argument normalisation only; the head is kept, no value is minted",
    ),
    (
        "UInt64.ofNat",
        "argument normalisation only; the head is kept, no value is minted",
    ),
    // tc/infer.rs: sets Lean's `m_eager_reduce` flag while checking the
    // argument — a reduction-strategy hint, never a value.
    (
        "eagerReduce",
        "reduction-strategy flag only (Lean parity), no value is minted",
    ),
    // tc/whnf_proof.rs: builds proof TERMS for the public `whnf_with_proof`
    // API; `add_decl` never calls it.
    (
        "Eq.refl",
        "proof-producing whnf API only; not on the add_decl path",
    ),
    (
        "Eq.trans",
        "proof-producing whnf API only; not on the add_decl path",
    ),
    (
        "Eq.symm",
        "proof-producing whnf API only; not on the add_decl path",
    ),
    (
        "Eq.subst",
        "proof-producing whnf API only; not on the add_decl path",
    ),
    (
        "congrArg",
        "proof-producing whnf API only; not on the add_decl path",
    ),
    (
        "congrFun'",
        "proof-producing whnf API only; not on the add_decl path",
    ),
    (
        "congr",
        "proof-producing whnf API only; not on the add_decl path",
    ),
    // tc/infer_zfc.rs: ZFC mode only.
    (
        "ZFC.Set",
        "ZFC mode only; the replay runs in the default mode",
    ),
    // tc/reduction/kan.rs, directed.rs, cofib.rs: gated on
    // `mode.has_cubical_layer()` / `CleanMode::Directed`, or reachable only
    // from a cubical expression node no Lean declaration contains.
    ("Glue", "cubical mode only"),
    ("glue", "cubical mode only"),
    ("unglue", "cubical mode only"),
    ("Glue.Sys", "cubical mode only"),
    ("Glue.Sys.cons", "cubical mode only"),
    ("Glue.Sys.nil", "cubical mode only"),
    ("System.cons", "cubical mode only"),
    ("System.nil", "cubical mode only"),
    ("I.max", "cubical mode only"),
    ("I.min", "cubical mode only"),
    ("I.neg", "cubical mode only"),
    ("Sigma", "cubical mode only"),
    ("Sigma.elim", "cubical mode only"),
    ("Sigma.mk", "cubical mode only"),
    ("Equiv", "cubical mode only"),
    ("Equiv.mk", "cubical mode only"),
    ("Equiv.fwd", "cubical mode only"),
    ("Equiv.bwd", "cubical mode only"),
    ("Equiv.idEquiv", "cubical mode only"),
    ("Equiv.toIsEquiv", "cubical mode only"),
    ("Cofib.top", "cubical mode only"),
    ("Cofib.bot", "cubical mode only"),
    ("Cofib.eq0", "cubical mode only"),
    ("Cofib.eq1", "cubical mode only"),
    ("Cofib.and", "cubical mode only"),
    ("Cofib.or", "cubical mode only"),
    (
        "u",
        "a universe-parameter name in a cubical/directed builder, not a constant",
    ),
    ("Dir.𝟚", "directed mode only"),
    ("Dir.0₂", "directed mode only"),
    ("Dir.1₂", "directed mode only"),
    ("Dir.le", "directed mode only"),
    ("Dir.Hom", "directed mode only"),
    ("Dir.Hom2", "directed mode only"),
    ("Dir.homLam", "directed mode only"),
    ("Dir.homApp", "directed mode only"),
    ("Dir.degen2", "directed mode only"),
    ("Empty", "directed mode only"),
    ("Unit", "directed mode only"),
];

/// Label of the table [`ExtensionBindings::pinned`] returns: the union of the
/// reviewed worlds in `extension_binding_pins.rs`, in their order.
pub const PINNED_TABLE_LABEL: &str =
    "lean-v4.8.0-core | lean-v4.30.0-rc2-core | clean-import+lean-v4.30.0-rc2-core | lean-v4.35.0-literals-div-mod";

/// One reviewed fingerprint for a key, and the world that pinned it.
#[derive(Debug, Clone)]
struct Pin {
    world: String,
    digest: [u8; 32],
}

/// The table the replay compares extension keys against.
#[derive(Debug, Clone)]
pub(crate) struct ExtensionBindings {
    label: String,
    pinned: bool,
    /// Every reviewed fingerprint of each key; the key binds to any of them.
    table: BTreeMap<Name, Vec<Pin>>,
}

impl Default for ExtensionBindings {
    fn default() -> Self {
        Self::pinned()
    }
}

impl ExtensionBindings {
    /// The pinned table — the union of the reviewed worlds in
    /// `extension_binding_pins.rs` — the only one that may ground a
    /// `Certified`-class claim or promote a trust-ledger origin.
    #[must_use]
    pub(crate) fn pinned() -> Self {
        Self::from_rows(
            PINNED_TABLE_LABEL,
            true,
            PINNED_WORLDS.iter().flat_map(|world| {
                world
                    .rows
                    .iter()
                    .map(move |(name, hex)| (world.label, Name::from_string(name), decode_hex(hex)))
            }),
        )
    }

    fn from_rows<'w>(
        label: &str,
        pinned: bool,
        rows: impl IntoIterator<Item = (&'w str, Name, [u8; 32])>,
    ) -> Self {
        let mut table: BTreeMap<Name, Vec<Pin>> = BTreeMap::new();
        for (world, name, digest) in rows {
            let pins = table.entry(name).or_default();
            // Two worlds that pin one digest vouch for one cone (the `Nat`
            // family is the same in v4.8.0 and v4.30.0-rc2): one row, both
            // worlds named on it.
            match pins.iter_mut().find(|p| p.digest == digest) {
                Some(pin) => {
                    pin.world.push_str(" + ");
                    pin.world.push_str(world);
                }
                None => pins.push(Pin {
                    world: world.to_string(),
                    digest,
                }),
            }
        }
        Self {
            label: label.to_string(),
            pinned,
            table,
        }
    }

    /// A table binding every extension key to whatever `env` declares for it.
    ///
    /// This is how a pinned world is produced (over that world's closure), and
    /// how a test states the honest meaning of a key. A replay run under a
    /// table derived from the environment it checks binds NOTHING — it is the
    /// ungated behaviour — so such a table is never [`Self::is_pinned`], and a
    /// pass under it promotes nothing.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn derive_from(env: &Environment, label: &str) -> Self {
        let mut fp = Fingerprinter::new(env);
        let rows: Vec<(&str, Name, [u8; 32])> = EXTENSION_KEYS
            .iter()
            .map(|k| Name::from_string(k.name))
            .filter(|name| declares(env, name))
            .map(|name| {
                let digest = fp.constant(&name);
                (label, name, digest)
            })
            .collect();
        Self::from_rows(label, false, rows)
    }

    /// The union of `tables`, under `label` — never pinned, whatever the
    /// parts were: how a test states "a key binds to any world's row".
    #[cfg(test)]
    #[must_use]
    pub(crate) fn union(label: &str, tables: &[&Self]) -> Self {
        let rows: Vec<(String, Name, [u8; 32])> = tables
            .iter()
            .flat_map(|t| {
                t.table.iter().flat_map(|(name, pins)| {
                    pins.iter()
                        .map(move |p| (p.world.clone(), name.clone(), p.digest))
                })
            })
            .collect();
        Self::from_rows(
            label,
            false,
            rows.iter()
                .map(|(world, name, digest)| (world.as_str(), name.clone(), *digest)),
        )
    }

    /// The table's label, carried into the report.
    #[must_use]
    pub(crate) fn label(&self) -> &str {
        &self.label
    }

    /// Whether this is the pinned table (not one derived at run time).
    #[must_use]
    pub(crate) fn is_pinned(&self) -> bool {
        self.pinned
    }

    /// The names this table binds.
    #[cfg(test)]
    pub(crate) fn bound_names(&self) -> impl Iterator<Item = &Name> {
        self.table.keys()
    }
}

#[cfg(test)]
fn declares(env: &Environment, name: &Name) -> bool {
    env.get_const(name).is_some()
        || env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
}

/// Where the kernel matches `name` by name, if it is an extension key.
pub(super) fn extension_hook(name: &Name) -> Option<&'static str> {
    static KEYS: std::sync::LazyLock<BTreeMap<Name, &'static str>> =
        std::sync::LazyLock::new(|| {
            EXTENSION_KEYS
                .iter()
                .map(|k| (Name::from_string(k.name), k.hook))
                .collect()
        });
    KEYS.get(name).copied()
}

/// The outcome of gating one extension key.
pub(super) enum BindingVerdict {
    /// The declaration's fingerprint is a pinned one.
    Bound,
    /// It is not (or the table has no row for this key).
    Mismatch {
        expected: Option<String>,
        found: String,
    },
}

/// Gate one key's fingerprint against `bindings`.
///
/// The fingerprint is taken over the SOURCE declarations. That is exactly what
/// the replay admits: every constant the fingerprint reaches is in the key's
/// cone, is re-admitted from those same bytes before the key is, and a family
/// is admitted from the same `add_inductive_core` input the fingerprint
/// hashes (its recursors are regenerated from it, so they are not hashed).
///
/// A key binds when its fingerprint is ANY reviewed world's row for it (see
/// `extension_binding_pins.rs` for why a union of worlds is sound); a refusal
/// names every row it was compared against, world by world.
pub(super) fn check_binding(
    bindings: &ExtensionBindings,
    name: &Name,
    found: &[u8; 32],
) -> BindingVerdict {
    match bindings.table.get(name) {
        Some(pins) if pins.iter().any(|p| &p.digest == found) => BindingVerdict::Bound,
        pins => BindingVerdict::Mismatch {
            expected: pins.map(|pins| {
                pins.iter()
                    .map(|p| format!("{}: {}", p.world, encode_hex(&p.digest)))
                    .collect::<Vec<_>>()
                    .join(" | ")
            }),
            found: encode_hex(found),
        },
    }
}

pub(super) fn encode_hex(d: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    d.iter().fold(String::with_capacity(64), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    })
}

fn decode_hex(s: &str) -> [u8; 32] {
    let mut out = [0u8; 32];
    assert_eq!(s.len(), 64, "pinned fingerprint must be 64 hex digits: {s}");
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[2 * i..2 * i + 2], 16)
            .unwrap_or_else(|_| panic!("pinned fingerprint is not hex: {s}"));
    }
    out
}

#[cfg(test)]
#[path = "extension_binding_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "kernel_built_name_tests.rs"]
mod kernel_built_name_tests;

#[cfg(test)]
#[path = "by_name_census_tests.rs"]
mod by_name_census_tests;

#[cfg(test)]
#[path = "extension_binding_lean_tests.rs"]
mod lean_world_tests;

#[cfg(test)]
#[path = "extension_binding_lean435_tests.rs"]
mod lean435_tests;

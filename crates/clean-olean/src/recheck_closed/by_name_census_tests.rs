// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Every name the replay's kernel code mentions BY NAME, over the WHOLE
//! kernel crate, is gated or explained.
//!
//! # Why this replaced a `tc/`-only scan as the authority
//!
//! Round 23's scan read `clean-kernel/src/tc` for `Name::from_string("…")`.
//! Three kinds of by-name reference escaped it, all outside `tc/` or in
//! another spelling:
//!
//! * `quot.rs` builds `Quot.lift`/`Quot.sound`'s types around the name `Eq`
//!   (the round-23 verifier's false accept);
//! * `inductive/mod.rs` compares `name.to_string() == "optParam"` (and three
//!   more) — a string comparison, no `Name::from_string` at all;
//! * `tc/reduction/mod.rs` matches `Quot.lift`/`Quot.ind` through
//!   `crate::quot::names`, statics defined in another file.
//!
//! # What this measures
//!
//! [`Census::build`] lexes every non-test source file of `clean-kernel`,
//! finds every function, static, const and `macro_rules!` item, and computes
//! which of them the replay can REACH from the kernel entry points it calls
//! ([`ENTRY_POINTS`]). Resolution over-approximates, never under-: a method
//! call resolves to every method of that name on every type the reached code
//! mentions (plus trait defaults), a bare call to every free function of that
//! name when the calling file defines none, a SCREAMING_CASE identifier to
//! every static/const of that name, and every reached type's
//! implicitly-called trait methods (`fmt`, `eq`, `hash`, `drop`, `deref`, …)
//! are reached too. Every identifier-shaped string or byte-string literal in
//! a reached item stays in the inventory. Occurrence-local syntax identifies
//! byte-array initializers, build-environment keys, let-binder labels and
//! persistent-extension registry/wire names; everything else stays a possible
//! by-name reference. No file or spelling is exempted by these roles.
//!
//! Each one must be (a) an extension key (gated by fingerprint), (b) a
//! quotient primitive (kernel-built, installed only by `add_quot`), or (c)
//! listed in [`EXPLAINED`] for THAT source file with the reason it cannot give
//! an admitted name a second meaning. A new reachable by-name reference, or
//! an old one at a new site, fails the test until someone decides.
//!
//! The over-approximation was checked against the linker:
//! `scripts/replay_reachability_census.sh` links a binary that calls only
//! `recheck_closed` (no optimisation, dead code stripped) and compares its
//! symbol table with this scan's reached set (`CLEAN_BY_NAME_CENSUS_DUMP`).

use super::EXTENSION_KEYS;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

#[path = "by_name_census_tests_controls.rs"]
mod controls;
#[path = "by_name_census_tests_identity.rs"]
mod identity;
#[cfg(test)]
#[path = "by_name_census_tests_reach.rs"]
mod reach;
#[path = "by_name_census_tests_roles.rs"]
mod roles;
#[cfg(test)]
#[path = "by_name_census_tests_scan.rs"]
mod scan;
use reach::Census;

/// The replay's own source files (this crate). Every kernel call they make
/// is a root of the census, resolved like any other call.
const REPLAY_SOURCES: &[&str] = &[
    "src/recheck_closed.rs",
    "src/recheck_closed/drive.rs",
    "src/recheck_closed/replay.rs",
    "src/recheck_closed/fingerprint.rs",
    "src/recheck_closed/extension_binding.rs",
    "src/recheck_closed/imported.rs",
    "src/recheck_closed/level.rs",
];

/// Kernel entry points the census must find among those roots: `(owner, fn)`.
/// A liveness check on the resolution, and roots in their own right.
///
/// `Environment::get_native_reducer` left this list on 2026-09-28, when the
/// gate stopped calling it (`drive.rs`: the `NativeReducerCollision` refusal
/// the kernel's native-fold authority made stale). The kernel's own call —
/// `TypeChecker::native_reducer_for`, behind the authority — is reached from
/// the checker entry points below, and the census asserts that it still is.
const ENTRY_POINTS: &[(&str, &str)] = &[
    ("Environment", "add_decl"),
    ("Environment", "add_inductive_core"),
    ("Environment", "add_inductive"),
    ("Environment", "add_quot"),
    ("TypeChecker", "new"),
    ("TypeChecker", "is_def_eq"),
];

/// Trait methods a reached type can have called WITHOUT their name appearing
/// at the call site (operators, formatting, drop glue, iteration, `?`, …):
/// `(trait, method)`. Each reaches the method of that name in every
/// `impl Trait for T` block of a reached `T` — not an inherent method that
/// merely shares the name.
const IMPLICIT_METHODS: &[(&str, &str)] = &[
    ("Display", "fmt"),
    ("Debug", "fmt"),
    ("PartialEq", "eq"),
    ("PartialEq", "ne"),
    ("PartialOrd", "partial_cmp"),
    ("PartialOrd", "lt"),
    ("PartialOrd", "le"),
    ("PartialOrd", "gt"),
    ("PartialOrd", "ge"),
    ("Ord", "cmp"),
    ("Hash", "hash"),
    ("Drop", "drop"),
    ("Deref", "deref"),
    ("DerefMut", "deref_mut"),
    ("Index", "index"),
    ("IndexMut", "index_mut"),
    ("Clone", "clone"),
    ("Clone", "clone_from"),
    ("Default", "default"),
    ("Iterator", "next"),
    ("Iterator", "size_hint"),
    ("DoubleEndedIterator", "next_back"),
    ("ExactSizeIterator", "len"),
    ("From", "from"),
    ("Into", "into"),
    ("TryFrom", "try_from"),
    ("FromIterator", "from_iter"),
    ("IntoIterator", "into_iter"),
    ("Extend", "extend"),
    ("AsRef", "as_ref"),
    ("Borrow", "borrow"),
    ("Add", "add"),
    ("Sub", "sub"),
    ("Mul", "mul"),
    ("Div", "div"),
    ("Rem", "rem"),
    ("Neg", "neg"),
    ("Not", "not"),
    ("BitAnd", "bitand"),
    ("BitOr", "bitor"),
    ("BitXor", "bitxor"),
    ("Shl", "shl"),
    ("Shr", "shr"),
    ("AddAssign", "add_assign"),
    ("SubAssign", "sub_assign"),
    ("Serialize", "serialize"),
    ("Deserialize", "deserialize"),
    ("Error", "source"),
    ("Fn", "call"),
    ("FnMut", "call_mut"),
    ("FnOnce", "call_once"),
];

const NOT_A_NAME: &str = "not a constant name: a Debug/Display/serde label, a diagnostic string or a binder spelling for printing; nothing compares a declaration's name against it";
const OPTION: &str = "an `Environment` option key or value (`set_option`), read as a resource budget or profiler switch; no declaration name is compared against it";
const ENV_VAR: &str = "a process environment-variable name or a profiler frame label; no declaration name is compared against it";
const UNIV: &str =
    "a universe-PARAMETER name of a kernel-built or kernel-generated declaration, not a constant";
const SUFFIX: &str = "the suffix under which the kernel NAMES a declaration it generates from a family (`T.rec`, `T.casesOn`, …); a cone member of that name is compared against the regenerated one (`replay_family`), never believed";
const AUX: &str = "generated-auxiliary construction (`noConfusion`/`below`/`brecOn`): only under `GeneratedAuxDefs::Generate` (`add_inductive`; the closed replay uses `add_inductive_core`, `clean_families: false`), and every generated declaration is type-checked (`check_decl_readonly_strict` / `add_decl`) before it is installed, so a forged meaning of these names yields a checked declaration of that meaning, not a false accept";
const NATIVE: &str = "a native-reducer operand hook, consulted only AFTER `native_reducer_for(name)?` succeeds (tc/def_eq/delta_helpers.rs); the closed replay's environment installs no native reducer (asserted by `a_forged_bool_not_does_not_prove_false_through_the_default_replay`), and over a consumer's base (the imported-cone gate) a reducer fires only when the kernel's native-fold authority finds its head AND every name it recognizes canonical in the replay environment (`tc/fold_admission.rs` `registry_reducer_admitted`)";
const OFNAT: &str = "argument normalisation only (tc/def_eq/delta_helpers.rs): rebuilds `f (whnf arg)` with the SAME head, so the term stays def-eq to the original whatever `f` is; nothing is evaluated by name";
const EAGER: &str = "`eagerReduce` sets Lean's `m_eager_reduce` flag while checking the argument — a reduction-strategy hint, never a value";
const CUBICAL: &str = "cubical/directed/ZFC/impredicative-mode machinery: gated on the checker's `CleanMode` (the replay runs in the default classical mode) or reachable only from an expression node no Lean declaration contains";
const QUALITY: &str = "proof-quality lint (`assert_proof_nontrivial`, env/proof_quality.rs), run after the kernel admits a theorem and only under `CLEAN_STRICT_PROOF_QUALITY=1`: on a finding it REMOVES the declaration and returns an error; it can only refuse";
const FARKAS: &str = "reached only through the census's SCREAMING_CASE rule (`NAT_ADD`/`INT_ADD`/… also name `tc/reduction`'s statics); env/farkas_soundness.rs is not linked into the replay (scripts/replay_reachability_census.sh) and its names are Clean's own `Clean.Farkas.*` certificate constants";

const NATIVE_FOLD: &str = "a name-keyed native fold (a registered native reducer, the kernel-theory list of reducers Lean's theory admits, or the canonical-digest table that authorizes them): it fires only through `TypeChecker::native_reducer_for` (tc/config.rs), which needs the environment's native-reducer table — empty in the replay (`Environment::default()`, asserted by `a_forged_bool_not_does_not_prove_false_through_the_default_replay`) — AND the native-fold authority (env/native_fold_authority.rs, tc/fold_admission.rs), which admits a fold only when the constant's δ-closure digest is canonical; an admitted declaration of that name with any other content never folds";
const SORRY_BUILDER: &str = "installs Clean's own polymorphic `sorry` axiom (`init_sorry`), called by `Environment::new`, the prelude constructors and the nn-verify builders only; the replay starts from `Environment::default()` and admits declarations only through `add_decl` / `add_inductive_core` / `add_quot`";
const PROOF_TERM: &str = "names `Eq.refl` in a proof TERM the proof-producing WHNF returns (tc/whnf_proof.rs); nothing is evaluated or believed by that name — a consumer type-checks the returned term against the environment's actual `Eq.refl` — and it is reached only through the census's SCREAMING_CASE rule (`EQ_REFL`)";

/// Every by-name reference at a reachable site that is neither an extension
/// key nor a quotient primitive: `(file, literals, reason)`.
///
/// The reason says why the literal cannot give a name the replay admits a
/// second meaning — it is not a constant name at all, or the code that uses
/// it cannot run in the closed replay, or it only BUILDS a term the kernel
/// then type-checks before anything is installed, or it can only add a
/// rejection. Measured 2026-09-25 (round 24); a new site fails the test.
#[rustfmt::skip]
pub(super) const EXPLAINED: &[(&str, &[&str], &str)] = &[
    (
        "env/matcher.rs",
        &["camelCase"],
        NOT_A_NAME,
    ),
    (
        "tc/fold_admission.rs",
        &["List", "String.mk"],
        super::LEGACY_STRING_LAYOUT,
    ),
    // Wire tags select Name/Level constructors while decoding a source packet.
    // Decoded constant names remain data; none of these tags names a constant
    // whose identity could authorize a kernel reduction or declaration.
    (
        "env/builtin_bundle.rs",
        &["anon", "imax", "max", "num", "param", "str", "succ", "zero"],
        NOT_A_NAME,
    ),
    (
        "env/native_fold_digest.rs",
        &["A", "C", "D", "I", "O", "Q", "R", "T", "ctors"],
        NOT_A_NAME,
    ),
    (
        "env/native_reducers_decidable_ext.rs",
        &["And", "And.intro", "And.left", "And.right", "Bool", "Decidable.decide", "Decidable.isFalse", "Decidable.isTrue", "Eq.refl", "False", "Int.decEq", "Int.decLe", "Int.decLt", "Int.noConfusion", "Nat.decLe", "Nat.decLt", "Nat.ne_of_beq_false", "Not", "Or", "Or.inl", "Or.inr", "Or.rec", "decide", "instDecidableAnd", "instDecidableEqInt", "instDecidableLeInt", "instDecidableLtInt", "instDecidableNot", "instDecidableOr"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_init.rs",
        &["Array.mk", "Array.size", "Decidable.isFalse", "Decidable.isTrue", "List.getLast!", "List.length", "Ord.compare", "Ordering.eq", "Ordering.gt", "Ordering.lt", "compareOfLessAndEq", "dite", "instOrdNat", "ite"],
        NATIVE_FOLD,
    ),
    (
        "env/native_fold_canon.rs",
        &["BEq.beq", "BitVec.ofNat", "BitVec.ofNatLT", "HAdd.hAdd", "HAppend.hAppend", "HDiv.hDiv", "HMod.hMod", "HMul.hMul", "HPow.hPow", "HSub.hSub", "OfNat.ofNat", "Ord.compare", "UInt16.ofNat", "UInt32.ofNat", "UInt64.ofNat", "UInt8.ofNat", "instAppendString", "instBEqBool", "instBEqChar", "instBEqFin", "instBEqInt", "instBEqNat", "instBEqString", "instBEqUInt16", "instBEqUInt32", "instBEqUInt64", "instBEqUInt8", "instBEqUSize", "instHAddNat", "instHAddNatNatNat", "instHAppendOfAppend", "instHAppendString", "instHAppendStringStringString", "instHDivNat", "instHDivNatNatNat", "instHModNat", "instHModNatNatNat", "instHMulNatNatNat", "instHPowNatNatNat", "instHSubNatNatNat", "instOfNatBitVec", "instOfNatNat", "instOrdNat", "native_fold_canon.tsv"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_beq_shortcircuit.rs",
        &["BEq.beq", "instBEqBool", "instBEqChar", "instBEqFin", "instBEqInt", "instBEqNat", "instBEqString", "instBEqUInt16", "instBEqUInt32", "instBEqUInt64", "instBEqUInt8", "instBEqUSize"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_bitvec.rs",
        &["BitVec", "BitVec.add", "BitVec.and", "BitVec.mul", "BitVec.neg", "BitVec.not", "BitVec.ofFin", "BitVec.ofNatLT", "BitVec.or", "BitVec.shiftLeft", "BitVec.sle", "BitVec.slt", "BitVec.sub", "BitVec.udiv", "BitVec.ule", "BitVec.ult", "BitVec.umod", "BitVec.ushiftRight", "BitVec.xor", "Fin.mk", "ISize.ofUSize", "ISize.toBitVec", "ISize.toUSize", "Int16.ofUInt16", "Int16.toBitVec", "Int16.toUInt16", "Int32.ofUInt32", "Int32.toBitVec", "Int32.toUInt32", "Int64.ofUInt64", "Int64.toBitVec", "Int64.toUInt64", "Int8.ofUInt8", "Int8.toBitVec", "Int8.toUInt8", "OfNat.ofNat", "UInt16.ofBitVec", "UInt16.toBitVec", "UInt32.ofBitVec", "UInt32.toBitVec", "UInt64.ofBitVec", "UInt64.toBitVec", "UInt8.ofBitVec", "UInt8.toBitVec", "USize.ofBitVec", "USize.toBitVec", "instOfNatBitVec", "instOfNatNat"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_char.rs",
        &["BitVec.ofFin", "BitVec.ofNat", "BitVec.ofNatLT", "Char.decEq", "Char.decLe", "Char.isAlpha", "Char.isDigit", "Char.isLower", "Char.isUpper", "Char.isWhitespace", "Char.mk", "Char.toLower", "Char.toNat", "Char.toUpper", "Fin.mk", "UInt32.ofBitVec"],
        NATIVE_FOLD,
    ),
    (
        "env/kernel_theory.rs",
        &["BitVec.sle", "BitVec.slt", "BitVec.toNat", "BitVec.ule", "BitVec.ult", "Bool.and", "Bool.decEq", "Bool.not", "Bool.or", "Bool.xor", "Char.isAlpha", "Char.isDigit", "Char.isLower", "Char.isUpper", "Char.isWhitespace", "Char.toLower", "Char.toNat", "Char.toUpper", "Int.natAbs", "Int.neg", "Int.toNat", "Lean.Name.append", "Lean.Name.beq", "Lean.Name.mkNum", "Lean.Name.mkStr", "Nat.blt", "String.append", "String.decEq", "String.isEmpty", "String.length", "String.singleton", "String.utf8ByteSize"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers.rs",
        &["Bool", "Bool.and", "Bool.decEq", "Bool.noConfusion", "Bool.not", "Bool.or", "Bool.xor", "Char.toNat", "Decidable.isFalse", "Decidable.isTrue", "Eq.refl", "False", "Nat.decEq", "Nat.le", "Nat.le_of_ble_eq_true", "Nat.lt", "Nat.ne_of_beq_false", "Nat.not_le_of_ble_eq_false", "String.append", "String.beq", "String.decEq", "String.isEmpty", "String.length", "String.push", "String.utf8ByteSize", "congrArg", "lt"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_decidable.rs",
        &["Bool", "Fin.decEq", "instDecidableEqBool", "instDecidableEqFin", "instDecidableEqNat", "instDecidableEqString", "instDecidableNatLe", "instDecidableNatLt"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_bool_ext.rs",
        &["Bool.beq"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_decidable_aliases.rs",
        &["Bool.decEq", "Nat.decEq", "String.decEq", "instDecidableEqChar", "instDecidableEqFloat", "instDecidableEqUInt16", "instDecidableEqUInt32", "instDecidableEqUInt64", "instDecidableEqUInt8"],
        NATIVE_FOLD,
    ),
    (
        "env/farkas_soundness.rs",
        &["Clean.Farkas.intNeg"],
        FARKAS,
    ),
    (
        "env/native_reducers_int.rs",
        &["Decidable.isFalse", "Decidable.isTrue", "Int.beq", "Int.ble", "Int.blt", "Int.decEq", "Int.div", "Int.mod", "Int.natAbs", "Int.neg", "Int.toNat"],
        NATIVE_FOLD,
    ),
    // Reached since 3809edf31 through `native_fold_authority::fold_key_universe`,
    // which runs every registration (`ensure_native_reducers`) on a SCRATCH
    // environment only to read the registered NAMES, then drops it -- no
    // TypeChecker ever consults that table. The UInt carrier/literal names
    // (`UInt8`, `BitVec.ofFin`, `Fin.mk`, `OfNat.ofNat`, `instOfNatNat`, …) are
    // read inside the decEq/decLt reducers, and `lt` names the wrapper
    // relation their witness is built at (`native_reducers.rs`
    // `mk_wrapper_lt_dec`): all of it runs only once `native_reducer_for`
    // picked a reducer, which the replay's empty table never does.
    // Linker census 2026-09-29: 0 linked kernel items unreached after the
    // census learned `#[path]` modules and macro-generated reducers.
    (
        "env/native_reducers_uint.rs",
        &["BitVec.ofFin", "BitVec.ofNat", "BitVec.ofNatLT", "Decidable.isFalse", "Decidable.isTrue", "Fin.mk", "OfNat.ofNat", "UInt16", "UInt16.add", "UInt16.beq", "UInt16.ble", "UInt16.blt", "UInt16.complement", "UInt16.decEq", "UInt16.decLt", "UInt16.div", "UInt16.land", "UInt16.lor", "UInt16.mod", "UInt16.mul", "UInt16.shiftLeft", "UInt16.shiftRight", "UInt16.sub", "UInt16.toNat", "UInt16.xor", "UInt32", "UInt32.add", "UInt32.beq", "UInt32.ble", "UInt32.blt", "UInt32.complement", "UInt32.decEq", "UInt32.decLt", "UInt32.div", "UInt32.land", "UInt32.lor", "UInt32.mod", "UInt32.mul", "UInt32.shiftLeft", "UInt32.shiftRight", "UInt32.sub", "UInt32.toNat", "UInt32.xor", "UInt64", "UInt64.add", "UInt64.beq", "UInt64.ble", "UInt64.blt", "UInt64.complement", "UInt64.decEq", "UInt64.decLt", "UInt64.div", "UInt64.land", "UInt64.lor", "UInt64.mod", "UInt64.mul", "UInt64.shiftLeft", "UInt64.shiftRight", "UInt64.sub", "UInt64.toNat", "UInt64.xor", "UInt8", "UInt8.add", "UInt8.beq", "UInt8.ble", "UInt8.blt", "UInt8.complement", "UInt8.decEq", "UInt8.decLt", "UInt8.div", "UInt8.land", "UInt8.lor", "UInt8.mod", "UInt8.mul", "UInt8.shiftLeft", "UInt8.shiftRight", "UInt8.sub", "UInt8.toNat", "UInt8.xor", "instOfNatNat"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_float.rs",
        &["Decidable.isTrue", "Eq.refl", "Float", "Float.abs", "Float.add", "Float.beq", "Float.ble", "Float.blt", "Float.ceil", "Float.decEq", "Float.decLe", "Float.decLt", "Float.div", "Float.floor", "Float.isFinite", "Float.isInf", "Float.isNaN", "Float.mk", "Float.mul", "Float.neg", "Float.ofInt", "Float.ofNat", "Float.ofScientific", "Float.round", "Float.sqrt", "Float.sub", "Float.toString", "Float.toUInt16", "Float.toUInt32", "Float.toUInt64", "Float.toUInt8", "Float.val", "NaN", "inf"],
        NATIVE_FOLD,
    ),
    (
        "tc/reduction/directed.rs",
        &["Dir.Hom", "Dir.Hom2", "Dir.degen2", "Dir.𝟚", "u"],
        CUBICAL,
    ),
    (
        "tc/cubical_authority.rs",
        &["Dir.degen2"],
        CUBICAL,
    ),
    (
        "tc/whnf_proof.rs",
        &["Eq.refl"],
        PROOF_TERM,
    ),
    (
        "tc/reduction/kan.rs",
        &["Equiv", "Equiv.toIsEquiv", "Glue.Sys", "u"],
        CUBICAL,
    ),
    (
        "env/native_reducers_uint_conv.rs",
        &["Fin.val", "UInt16.toUInt32", "UInt16.toUInt64", "UInt16.toUInt8", "UInt16.toUSize", "UInt32.toUInt16", "UInt32.toUInt64", "UInt32.toUInt8", "UInt32.toUSize", "UInt64.toUInt16", "UInt64.toUInt32", "UInt64.toUInt8", "UInt64.toUSize", "UInt8.toUInt16", "UInt8.toUInt32", "UInt8.toUInt64", "UInt8.toUSize", "USize.toUInt16", "USize.toUInt32", "USize.toUInt64", "USize.toUInt8"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_float_to_rat.rs",
        &["Float.mk", "Float.toRatExact", "Float.ulpExact", "Rat.mk", "Rat.roundToNearestEven"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_hetero_shortcircuit.rs",
        &["HAdd.hAdd", "HAppend.hAppend", "HDiv.hDiv", "HMod.hMod", "HMul.hMul", "HPow.hPow", "HSub.hSub", "instAppendString", "instHAddNat", "instHAddNatNatNat", "instHAppendOfAppend", "instHAppendString", "instHAppendStringStringString", "instHDivNat", "instHDivNatNatNat", "instHModNat", "instHModNatNatNat", "instHMulNatNatNat", "instHPowNatNatNat", "instHSubNatNatNat"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_sint.rs",
        &["ISize.add", "ISize.beq", "ISize.ble", "ISize.blt", "ISize.decEq", "ISize.decLe", "ISize.decLt", "ISize.div", "ISize.mod", "ISize.mul", "ISize.sub", "Int16.add", "Int16.beq", "Int16.ble", "Int16.blt", "Int16.decEq", "Int16.decLe", "Int16.decLt", "Int16.div", "Int16.mod", "Int16.mul", "Int16.sub", "Int32.add", "Int32.beq", "Int32.ble", "Int32.blt", "Int32.decEq", "Int32.decLe", "Int32.decLt", "Int32.div", "Int32.mod", "Int32.mul", "Int32.sub", "Int64.add", "Int64.beq", "Int64.ble", "Int64.blt", "Int64.decEq", "Int64.decLe", "Int64.decLt", "Int64.div", "Int64.mod", "Int64.mul", "Int64.sub", "Int8.add", "Int8.beq", "Int8.ble", "Int8.blt", "Int8.decEq", "Int8.decLe", "Int8.decLt", "Int8.div", "Int8.mod", "Int8.mul", "Int8.sub", "instDecidableEqISize", "instDecidableEqInt16", "instDecidableEqInt32", "instDecidableEqInt64", "instDecidableEqInt8"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_name.rs",
        &["Lean.Name.anonymous", "Lean.Name.append", "Lean.Name.beq", "Lean.Name.hash", "Lean.Name.mkNum", "Lean.Name.mkStr", "Lean.Name.num", "Lean.Name.str", "Lean.Name.toString"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_arith.rs",
        &["Nat.blt", "UInt32.add", "UInt32.mul", "UInt32.sub"],
        NATIVE_FOLD,
    ),
    (
        "env/native_fold_authority.rs",
        &["NativeFoldAuthorityCache", "boundaries", "identity"],
        NOT_A_NAME,
    ),
    (
        "env/native_reducers_string.rs",
        &["String.atEnd", "String.decLt", "String.drop", "String.extract", "String.front", "String.get", "String.hash", "String.intercalate", "String.isPrefixOf", "String.next", "String.prev", "String.singleton", "String.take", "String.toLower", "String.toUpper"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_string_ext.rs",
        &["String.containsSubstr", "String.endsWith", "String.replace", "String.startsWith", "String.substrEq", "String.trimLeft", "String.trimRight"],
        NATIVE_FOLD,
    ),
    (
        "env/native_reducers_platform.rs",
        &["System.Platform.getIsEmscripten", "System.Platform.getIsOSX", "System.Platform.getIsWindows", "macos"],
        NATIVE_FOLD,
    ),
    (
        "env/core/trust.rs",
        &["sorry", "u"],
        SORRY_BUILDER,
    ),
    (
        "cert/types.rs",
        &["App", "BVar", "Beta", "Bool", "Choice", "Const", "CubicalCoe", "CubicalEndpoint", "CubicalHComp", "CubicalI0", "CubicalI1", "CubicalInterval", "CubicalPath", "CubicalPathApp", "CubicalPathLam", "CubicalTransp", "DefEq", "DefEqStep", "DefEqSteps", "Delta", "Empty", "FVar", "Infinity", "Iota", "Lam", "Let", "LevelList", "Lit", "MData", "Metadata", "Name", "Pair", "Pi", "PowerSet", "Proj", "ProofCert", "Refl", "Replacement", "SProp", "Separation", "Singleton", "Sort", "Squash", "Struct", "Symm", "Trans", "Union", "ZFCComprehension", "ZFCMem", "ZFCSet", "Zeta", "actual_type", "arg_cert", "arg_level", "arg_type_cert", "base_cert", "binder_info", "body_cert", "body_level", "body_type", "body_type_cert", "children", "elem_cert", "eq_steps", "expected_type", "expr_cert", "expr_type", "field_type", "first", "first_name", "first_value", "first_value_kind", "fn_cert", "fn_type", "id", "idx", "inner", "inner_cert", "is_one", "kind", "left_cert", "len", "level", "levels", "lit", "metadata", "name", "path_cert", "path_type", "phi_cert", "pred_cert", "prefix", "r_cert", "result_type", "right_cert", "s_cert", "set_cert", "struct_name", "ty_cert", "ty_level", "type_", "type_cert", "u_cert", "value_cert", "var_ty_cert"],
        NOT_A_NAME,
    ),
    (
        "cert/verifier/modes.rs",
        &["ZFC.Set"],
        CUBICAL,
    ),
    // R107 moved these option reads from `env/decl_add.rs` into
    // `Environment::checker_settings` (`env/mod.rs`); the row moved with them.
    (
        "env/mod.rs",
        &["maxHeartbeats", "profileHeartbeats", "tcMaxCacheEntries", "true"],
        OPTION,
    ),
    (
        "env/farkas_soundness.rs",
        &["Clean.Farkas.Int", "Clean.Farkas.intAdd", "Clean.Farkas.intMul", "Clean.Farkas.natAdd", "Clean.Farkas.natMul"],
        FARKAS,
    ),
    (
        "env/inductive_below.rs",
        &["PProd", "below", "brecOn", "rec"],
        AUX,
    ),
    (
        "env/inductive_below_minors.rs",
        &["PProd", "PProd.mk", "PUnit", "PUnit.unit"],
        AUX,
    ),
    (
        "env/inductive_builder.rs",
        &["casesOn", "noConfusion", "noConfusionType", "rec", "recOn"],
        SUFFIX,
    ),
    (
        "env/inductive_fixed_indices.rs",
        &["u"],
        UNIV,
    ),
    (
        "env/inductive_nested_restore.rs",
        &["casesOn", "rec", "recOn"],
        SUFFIX,
    ),
    (
        "env/inductive_no_confusion.rs",
        &["Eq.ndrec", "Eq.refl", "HEq", "HEq.refl", "PUnit", "PUnit.unit", "casesOn", "eq_of_heq", "noConfusion", "noConfusionType"],
        AUX,
    ),
    (
        "env/inductive_no_confusion_hetero.rs",
        &["Eq.ndrec", "Eq.refl", "HEq", "HEq.refl", "PUnit", "PUnit.unit", "casesOn", "eq_of_heq", "noConfusionType"],
        AUX,
    ),
    (
        "env/inductive_recursor.rs",
        &["casesOn", "rec", "recOn"],
        SUFFIX,
    ),
    (
        "env/inductive_recursor_rules.rs",
        &["rec"],
        SUFFIX,
    ),
    (
        "env/native_reducers_bitvec.rs",
        &["BitVec.ofNat", "BitVec.toFin", "BitVec.toNat"],
        NATIVE,
    ),
    (
        "env/persistent_ext.rs",
        &["EnvExtensionStates", "active_count"],
        NOT_A_NAME,
    ),
    (
        "env/proof_quality.rs",
        &["CLEAN_STRICT_PROOF_QUALITY", "Eq.mp", "Eq.mpr", "Eq.refl", "Eq.subst", "Eq.symm", "Eq.trans", "HEq", "HEq.refl", "congr", "congrArg", "congrFun", "id", "rfl"],
        QUALITY,
    ),
    (
        "expr/display.rs",
        &["A", "And", "BEq.beq", "Exists", "GE.ge", "GT.gt", "HAdd.hAdd", "HAppend.hAppend", "HDiv.hDiv", "HMod.hMod", "HMul.hMul", "HPow.hPow", "HSub.hSub", "Iff", "LE.le", "LT.lt", "Ne", "Neg.neg", "Not", "OfNat.ofNat", "Or", "P", "Prop", "SProp", "Type", "_", "f", "i", "i0", "i1", "u", "x"],
        NOT_A_NAME,
    ),
    (
        "expr/kind.rs",
        &["CubicalI0", "CubicalI1", "CubicalInterval", "SProp", "level_vec_serde"],
        NOT_A_NAME,
    ),
    (
        "expr/mod.rs",
        &["expression"],
        NOT_A_NAME,
    ),
    (
        "level/mod.rs",
        &["IMax", "Level", "Max", "Param", "Succ", "Zero"],
        NOT_A_NAME,
    ),
    (
        "micro/types.rs",
        &["App", "BVar", "Const", "IMax", "Lam", "Let", "Lit", "Max", "Opaque", "Pi", "Proj", "Sort", "Succ", "Zero", "bits", "len", "low_u64_digits", "prefix"],
        NOT_A_NAME,
    ),
    (
        "mode.rs",
        &["Classical", "Constructive", "Cubical", "Directed", "Impredicative", "SetTheoretic"],
        NOT_A_NAME,
    ),
    (
        "name.rs",
        &["Anon", "NameInner", "Num", "Str", "name"],
        NOT_A_NAME,
    ),
    (
        "quot.rs",
        &["u", "v"],
        UNIV,
    ),
    (
        "tc/cert/infer_modes.rs",
        &["Cubical", "CubicalCoe", "CubicalHComp", "CubicalInterval", "CubicalPath", "CubicalPathApp", "CubicalPathLam", "CubicalTransp", "Impredicative", "SProp", "SetTheoretic", "Squash", "ZFCComprehension", "ZFCMem", "ZFCSet"],
        CUBICAL,
    ),
    (
        "tc/cert/mod.rs",
        &["ZFC.Set"],
        CUBICAL,
    ),
    (
        "tc/def_eq/delta_helpers.rs",
        &["Decidable.decide", "Nat.decEq", "UInt16.decEq", "UInt16.decLt", "UInt32.decEq", "UInt32.decLt", "UInt64.decEq", "UInt64.decLt", "UInt8.decEq", "UInt8.decLt", "USize.decEq", "USize.decLt", "decide", "instDecidableEqNat"],
        NATIVE,
    ),
    (
        "tc/def_eq/delta_helpers.rs",
        &["UInt16.ofNat", "UInt32.ofNat", "UInt64.ofNat", "UInt8.ofNat"],
        OFNAT,
    ),
    (
        "tc/heartbeat_profiler/types.rs",
        &["inferType", "isDefEq", "kernelWork", "whnf"],
        NOT_A_NAME,
    ),
    (
        "tc/infer.rs",
        &["eagerReduce"],
        EAGER,
    ),
    (
        "tc/infer_cubical.rs",
        &["Cubical", "CubicalCoe", "CubicalHComp", "CubicalInterval", "CubicalPath", "CubicalPathApp", "CubicalPathLam", "CubicalTransp"],
        CUBICAL,
    ),
    (
        "tc/infer_zfc.rs",
        &["Impredicative", "SProp", "SetTheoretic", "Squash", "ZFC.Set", "ZFCComprehension", "ZFCMem", "ZFCSet"],
        CUBICAL,
    ),
    (
        "tc/reduction/directed.rs",
        &["Dir.0₂", "Dir.1₂", "Dir.homApp", "Dir.homLam", "Dir.le", "Empty", "Unit"],
        CUBICAL,
    ),
    (
        "tc/reduction/kan.rs",
        &["Cofib.and", "Cofib.bot", "Cofib.eq0", "Cofib.eq1", "Cofib.or", "Cofib.top", "Equiv.bwd", "Equiv.fwd", "Equiv.idEquiv", "Equiv.mk", "Glue", "Glue.Sys.cons", "Glue.Sys.nil", "I.max", "I.min", "I.neg", "Sigma", "Sigma.elim", "Sigma.mk", "System.cons", "System.nil", "glue", "rec", "unglue"],
        CUBICAL,
    ),
    (
        "tc/reduction_stats.rs",
        &["CLEAN_TRACE_GRIND", "CLEAN_TRACE_GRIND_BT", "Sort", "beta_or_iota", "check_type", "fvar", "infer_impl", "infer_type", "is_def_eq_args", "is_def_eq_core", "is_def_eq_impl", "is_def_eq_proof_irrel", "is_def_eq_structural", "lazy_delta", "reduce_nat", "reduce_native", "reduction_stats", "try_branch_sharing", "try_iota_reduction", "try_unfold", "whnf_core", "whnf_core_inner", "whnf_impl", "whnf_outer", "whnf_with"],
        ENV_VAR,
    ),
    (
        "tc/reduction_stats/inference.rs",
        &["App", "BVar", "CLEAN_INFERENCE_STATS_EARLY", "Const", "CubicalCoe", "CubicalHComp", "CubicalI0", "CubicalI1", "CubicalInterval", "CubicalPath", "CubicalPathApp", "CubicalPathLam", "CubicalTransp", "FVar", "Lam", "Let", "Lit", "MData", "Pi", "Proj", "SProp", "Sort", "Squash", "ZFCComprehension", "ZFCMem", "ZFCSet"],
        ENV_VAR,
    ),
    (
        "tc/type_error.rs",
        &["Pi", "fun"],
        NOT_A_NAME,
    ),
    // The role column of the canonical-digest table (`FoldRole::as_str` /
    // `FoldRole::parse`): spellings of a row's role, never constant names.
    (
        "env/native_fold_canon.rs",
        &["definition", "fold", "refused"],
        NOT_A_NAME,
    ),
];

// ─────────────────────────────────────────────────────────────────────────────
// The test.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn every_by_name_reference_the_replay_can_reach_is_gated_or_explained() {
    let census = Census::build();
    // SELF-SKIP OK: opt-in dump for scripts/replay_reachability_census.sh
    // (CLEAN_BY_NAME_CENSUS_DUMP); only the diagnostic file write is conditional --
    // every census assertion below runs unconditionally.
    if let Ok(path) = std::env::var("CLEAN_BY_NAME_CENSUS_DUMP") {
        std::fs::write(&path, census.dump()).expect("write census dump");
    }
    let literals = census.literals();
    let sites = census.literal_sites();
    // SELF-SKIP OK: optional diagnostic write only; all assertions still run.
    if let Ok(path) = std::env::var("CLEAN_BY_NAME_LITERAL_DUMP") {
        let dump = sites
            .iter()
            .map(|((file, at), (s, role))| format!("{file}\t{at}\t{s}\t{role:?}\n"))
            .collect::<String>();
        std::fs::write(path, dump).expect("write literal roles");
    }
    // Classification keeps the original denominator. In particular all byte
    // literals remain visible, even when their direct role is byte data.
    let mut site_literals: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for ((file, _), (s, _)) in &sites {
        site_literals
            .entry(s.clone())
            .or_default()
            .insert(file.clone());
    }
    assert_eq!(
        literals, site_literals,
        "literal inventory lost an occurrence"
    );

    // Liveness: the kernel's own native-reducer lookup — behind the
    // native-fold authority — is reached from the checker, now that the gate
    // no longer calls `get_native_reducer` itself (see `ENTRY_POINTS`).
    for (owner, name) in [
        ("TypeChecker", "native_reducer_for"),
        ("Environment", "get_native_reducer"),
    ] {
        assert!(
            census.reaches_fn(owner, name),
            "the census must reach {owner}::{name} from the checker entry points"
        );
    }

    // Liveness: the scan must see each kind of site that escaped round 23.
    for (literal, file) in [
        ("Eq", "quot.rs"),
        ("optParam", "inductive/mod.rs"),
        ("Quot.lift", "quot.rs"),
        ("Nat.add", "tc/reduction/mod.rs"),
    ] {
        assert!(
            literals.get(literal).is_some_and(|f| f.contains(file)),
            "the census must reach `{literal}` in {file}; reached {} items",
            census.reached_count()
        );
    }

    let unclassified = census.unclassified();
    assert!(
        unclassified.is_empty(),
        "{} by-name references reachable from the replay are neither gated nor explained:\n{}",
        unclassified.len(),
        unclassified.join("\n")
    );

    // Every explanation is still needed (the table only shrinks). All stale
    // rows are reported at once, so the table can be pruned in one edit.
    let mut stale = Vec::new();
    for (file, row, _) in EXPLAINED {
        for literal in *row {
            if !literals.get(*literal).is_some_and(|f| f.contains(*file)) {
                stale.push(format!("{literal:?} in {file}"));
            }
        }
    }
    assert!(
        stale.is_empty(),
        "{} EXPLAINED rows are stale (the census no longer reaches them):\n{}",
        stale.len(),
        stale.join("\n")
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which prelude bodies the native path may compile.
//!
//! `constant_to_decl` lowers a value-bearing `Declaration::Opaque` exactly like
//! a definition. That is right for a USER `opaque` — Lean's compiler runs an
//! `opaque`'s value unless `@[extern]`/`@[implemented_by]` names another
//! implementation — and wrong for most of the builtin prelude's opaques, whose
//! value is a type-correct STAND-IN the kernel never unfolds: the constant's
//! meaning lives in a kernel native reducer, and the body only exists so the
//! declaration type-checks. Measured 2026-09-24 through `clean run`: the
//! prelude's `Int.div`/`Int.mod` were then `fun _ _ => Int.ofNat 0`, so
//! `IO.println (toString ((7 : Int) / 2))` printed `0` with exit status 0 where
//! pinned Lean v4.30.0-rc2 prints `3`; the `Float` family's bodies are
//! `Float.mk 0` / `UIntN.ofNat 0`, so `(2.5 * 4.0).toUInt64` printed `0` where
//! Lean prints `10`.
//!
//! A third spelling is a prelude definition whose value is REAL but whose
//! meaning is not Lean's for the programs that reach it. `Int.div`/`Int.mod`
//! are now Lean 4.8.0's T-rounding definitions (they compute in the kernel),
//! but the prelude's `/`/`%` on `Int` (`instHDivInt`/`instHModInt`) route
//! through them, where Lean's are the E-rounding `Int.ediv`/`Int.emod`:
//! `(-7 : Int) / 2` is `-3` here and `-4` in Lean.
//!
//! The same hazard has a second spelling: a prelude DEFINITION whose value is a
//! stand-in because nothing but instance synthesis was ever meant to read it.
//! Measured 2026-09-25: the core `Repr` instances were `Repr.mk (fun _ _ =>
//! "")` (`env/data_typeclasses_repr.rs`), so `IO.println (toString (repr 5))`
//! printed an empty line at exit 0 where Lean prints `5`. Since 2026-09-30
//! every `Repr` stub — those instances, `Option`/product ones, and the bodies
//! `deriving Repr` emits — renders through the prelude opaque
//! `Clean.Repr.render`, which the opaque audit classifies `Placeholder`; that
//! one entry refuses every program that would print a stub rendering,
//! including a derived structure's (`repr (P.mk 1)` printed `P` at exit 0
//! where Lean prints `{ x := 1 }`).
//!
//! The rule the native path now follows (see [`refuse_unfaithful_body`]):
//!
//! * an `Opaque` a SOURCE file of this build declared compiles from its value
//!   (Lean's own rule for an `opaque` with no extern);
//! * a prelude `Opaque` compiles only when [`PRELUDE_OPAQUE_AUDIT`] classifies
//!   its value as a genuine implementation;
//! * a prelude constant backed by a runtime shim never reaches this check —
//!   the PRIMITIVE_DENYLIST keeps it extern, so its value is never compiled
//!   (and a value-less opaque with no shim fails closed at link);
//! * a prelude `Definition` [`PRELUDE_DEFINITION_AUDIT`] classifies as a
//!   placeholder is refused;
//! * a prelude `Definition` [`PRELUDE_LEAN_DIVERGENT_AUDIT`] names is refused
//!   (its value is real, but a compiled program would not print what Lean
//!   prints);
//! * EVERY OTHER OPAQUE IS REFUSED, including one the table does not name and
//!   one an `.olean` import supplied. Since `docs/DECISIONS.md` R149 the
//!   loader registers an imported module's `@[extern]` / `@[implemented_by]`
//!   rows, and the dependency walk refuses such an `@[extern]` opaque, or
//!   redirects such an `@[implemented_by]` one to its implementation, before
//!   this check (`native_ffi_audit`). A kernel-value build (`clean extract`)
//!   redirects nothing, so there an imported `@[implemented_by]` opaque
//!   reaches this check, as an imported opaque that carries neither attribute
//!   does everywhere: both are refused, since no audit has classified the
//!   value.
//!
//! The tables are not the safety mechanism for opaques — the default is. They
//! are the AUDIT: `native_opaque_audit_tests` enumerates every value-bearing
//! `Opaque`, and every definition whose value ignores its arguments to return
//! a literal, in the environment the native path elaborates against, and fails
//! when one is unclassified or when an entry has gone stale, so the
//! classification cannot silently drift from the prelude.

use std::collections::HashSet;

use clean_kernel::{ConstantInfo, ConstantKind, Name};

use crate::native_build::is_primitive_denylisted;
use clean_compiler::mangle::mangle_name;

/// How the native path treats an audited prelude body.
///
/// The third classification the audit reports — "an extern with a real native
/// shim" — needs no entry: a shimmed constant is on the PRIMITIVE_DENYLIST, is
/// kept extern, and its value never reaches the compiler. The audit test
/// refuses a table entry for a denylisted constant as stale.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OpaqueRuntime {
    /// The value IS the constant's runtime behaviour, so compiling it is
    /// faithful.
    Genuine,
    /// The value is a type-correct stand-in; the kernel gives the constant its
    /// meaning through a native reducer, or nothing ever reads it.
    /// Compiling it prints a wrong answer.
    Placeholder,
    /// The value is a genuine definition the kernel computes with, but the
    /// programs that reach it mean something else in Lean (a prelude instance
    /// routes Lean notation to it), so a compiled program would print an
    /// answer Lean does not.
    LeanDivergent,
}

/// One audited prelude opaque.
#[derive(Debug)]
pub(crate) struct OpaqueAuditEntry {
    /// Fully-qualified constant name.
    pub(crate) name: &'static str,
    /// The classification.
    pub(crate) runtime: OpaqueRuntime,
    /// Why, in one line — what the value is and where the meaning lives.
    pub(crate) reason: &'static str,
}

const FLOAT_OP: &str = "value is the constant `Float.mk 0`; IEEE-754 semantics live in \
    native_reducers_float.rs and the native runtime has no faithful Float shim";
const FLOAT_PRED: &str = "value is `fun _ => Bool.false`; IEEE-754 classification lives in \
    native_reducers_float.rs";
const FLOAT_TO_UINT: &str = "value is `fun _ => UIntN.ofNat 0`; the float-to-unsigned \
    truncation lives in native_reducers_float.rs";

/// The audit of every value-bearing `Opaque` in the native path's base
/// environment (`Environment::with_prelude()` + `init_io_ops()`).
pub(crate) const PRELUDE_OPAQUE_AUDIT: &[OpaqueAuditEntry] = &[
    OpaqueAuditEntry {
        name: "Float.add",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_OP,
    },
    OpaqueAuditEntry {
        name: "Float.sub",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_OP,
    },
    OpaqueAuditEntry {
        name: "Float.mul",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_OP,
    },
    OpaqueAuditEntry {
        name: "Float.div",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_OP,
    },
    OpaqueAuditEntry {
        name: "Float.neg",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_OP,
    },
    OpaqueAuditEntry {
        name: "Float.round",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_OP,
    },
    OpaqueAuditEntry {
        name: "Float.ofNat",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_OP,
    },
    OpaqueAuditEntry {
        name: "Float.ofScientific",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_OP,
    },
    OpaqueAuditEntry {
        name: "Float.isNaN",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_PRED,
    },
    OpaqueAuditEntry {
        name: "Float.isInf",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_PRED,
    },
    OpaqueAuditEntry {
        name: "Float.isFinite",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_PRED,
    },
    OpaqueAuditEntry {
        name: "Float.toUInt8",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_TO_UINT,
    },
    OpaqueAuditEntry {
        name: "Float.toUInt16",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_TO_UINT,
    },
    OpaqueAuditEntry {
        name: "Float.toUInt32",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_TO_UINT,
    },
    OpaqueAuditEntry {
        name: "Float.toUInt64",
        runtime: OpaqueRuntime::Placeholder,
        reason: FLOAT_TO_UINT,
    },
    OpaqueAuditEntry {
        name: "Float.toString",
        runtime: OpaqueRuntime::Placeholder,
        reason: "value is `fun _ => \"\"` (data_typeclasses_tostring_float.rs); Lean's is the \
            `@[extern \"lean_float_to_string\"]` runtime renderer and the native runtime has no \
            faithful Float shim, so `toString (2.5 : Float)` would print an empty string",
    },
    OpaqueAuditEntry {
        name: "System.Platform.getNumBits",
        runtime: OpaqueRuntime::Genuine,
        reason: "value is Lean's own `fun _ => ⟨64, Or.inr rfl⟩` (Init/Prelude.lean), which \
            is what `lean_system_platform_nbits` returns on the 64-bit hosts the native \
            path targets",
    },
    OpaqueAuditEntry {
        name: "Clean.Repr.render",
        runtime: OpaqueRuntime::Placeholder,
        reason: "value is `fun _ _ => \"\"` (data_typeclasses_repr_compound.rs), the \
            renderer every default-prelude `Repr` stub and every `deriving Repr` body routes \
            through; Lean's `Repr` is `Std.Format`-valued and renders the value, so `repr 5` \
            would print an empty string",
    },
];

/// The audit of every prelude DEFINITION in the native path's base
/// environment whose value ignores its arguments to return a literal — the
/// shape a stand-in body takes. `native_opaque_audit_tests` re-derives that
/// set from the environment and requires this table to match it exactly.
///
/// Empty since 2026-09-30: its five entries were the core `Repr` instances,
/// whose values now route through the opaque `Clean.Repr.render` (refused
/// through [`PRELUDE_OPAQUE_AUDIT`]) instead of returning `""`.
pub(crate) const PRELUDE_DEFINITION_AUDIT: &[OpaqueAuditEntry] = &[];

const SILENT_PANIC: &str = "on a miss (an index out of range, an empty list) the prelude value \
    returns `default` silently, where Lean's implementation PANICS first: it prints a diagnostic \
    to stderr (`Error: index out of bounds` for `#[1, 2][5]!`, measured against pinned Lean \
    v4.30.0-rc2) and then returns `default`, so the native program would omit bytes Lean prints";

/// Prelude definitions whose value is kernel-faithful — Lean proves
/// `panic! = default` by `rfl` (`Init/GetElem.lean`'s `outOfBounds_eq_default`)
/// — but whose RUNTIME behaviour is not: Lean's compiled code prints a panic
/// diagnostic before returning `default`, and these values do not. Measured
/// 2026-09-25: `#[1, 2][5]!` printed `0` with empty stderr through `clean run`
/// where pinned Lean prints `0` and `Error: index out of bounds` on stderr.
/// The audit test requires every entry to name a definition the native base
/// environment really has.
pub(crate) const PRELUDE_SILENT_PANIC_AUDIT: &[OpaqueAuditEntry] = &[
    OpaqueAuditEntry {
        name: "GetElem?.getElem!",
        runtime: OpaqueRuntime::Placeholder,
        reason: SILENT_PANIC,
    },
    OpaqueAuditEntry {
        name: "List.head!",
        runtime: OpaqueRuntime::Placeholder,
        reason: SILENT_PANIC,
    },
    OpaqueAuditEntry {
        name: "List.get!",
        runtime: OpaqueRuntime::Placeholder,
        reason: SILENT_PANIC,
    },
    OpaqueAuditEntry {
        name: "Array.get!",
        runtime: OpaqueRuntime::Placeholder,
        reason: SILENT_PANIC,
    },
];

/// The opaque-audit entry for `name`, if the table has one.
pub(crate) fn audit_entry(name: &str) -> Option<&'static OpaqueAuditEntry> {
    PRELUDE_OPAQUE_AUDIT.iter().find(|entry| entry.name == name)
}

const INT_DIVMOD: &str = "legacy explicit T-rounding definition, whose native C \
    execution has not been admitted by this audit; the kernel computes with its \
    T-rounding value, while Int notation uses the separate checked E-rounding \
    Int.ediv/Int.emod definitions; changing notation does not qualify this native head";

/// Prelude definitions whose value is genuine — the kernel computes with it —
/// but whose native execution has not passed this fidelity boundary.
/// `Int.div`/`Int.mod` retain their explicit T-rounding definitions and this
/// refusal. The `/`/`%` instances now use separate checked E-rounding
/// definitions, which this table does not classify as T-rounding. The audit
/// test requires every entry to name a value-bearing definition the native
/// base environment really has.
pub(crate) const PRELUDE_LEAN_DIVERGENT_AUDIT: &[OpaqueAuditEntry] = &[
    OpaqueAuditEntry {
        name: "Int.div",
        runtime: OpaqueRuntime::LeanDivergent,
        reason: INT_DIVMOD,
    },
    OpaqueAuditEntry {
        name: "Int.mod",
        runtime: OpaqueRuntime::LeanDivergent,
        reason: INT_DIVMOD,
    },
];

/// The definition-audit entry for `name` — a stub-shaped value
/// ([`PRELUDE_DEFINITION_AUDIT`]), a silently-panicking one
/// ([`PRELUDE_SILENT_PANIC_AUDIT`]) or a Lean-divergent one
/// ([`PRELUDE_LEAN_DIVERGENT_AUDIT`]) — if any table has one.
pub(crate) fn definition_audit_entry(name: &str) -> Option<&'static OpaqueAuditEntry> {
    PRELUDE_DEFINITION_AUDIT
        .iter()
        .chain(PRELUDE_SILENT_PANIC_AUDIT)
        .chain(PRELUDE_LEAN_DIVERGENT_AUDIT)
        .find(|entry| entry.name == name)
}

/// A reached constant the native path refuses to compile, with the reason.
#[derive(Debug, thiserror::Error)]
pub(crate) enum UnfaithfulOpaque {
    /// A prelude opaque or definition whose value is a stand-in.
    #[error(
        "native build refuses `{name}` (reached from `{root}`): it is a prelude \
         declaration whose value is a placeholder, not an implementation — {reason}. \
         Compiling it would print a wrong answer with exit status 0, so this build is \
         refused (native-opaque-placeholder)."
    )]
    Placeholder {
        /// The refused constant.
        name: String,
        /// The declaration being built.
        root: String,
        /// The audit reason.
        reason: &'static str,
    },
    /// A prelude definition whose value is genuine but not what Lean runs for
    /// the programs that reach it.
    #[error(
        "native build refuses `{name}` (reached from `{root}`): it is a prelude \
         definition whose value the kernel computes with, but a compiled program would not \
         print what Lean prints — {reason}. This build is refused (native-lean-divergent)."
    )]
    LeanDivergent {
        /// The refused constant.
        name: String,
        /// The declaration being built.
        root: String,
        /// The audit reason.
        reason: &'static str,
    },
    /// An opaque neither the source files nor the audit vouch for.
    #[error(
        "native build refuses `{name}` (reached from `{root}`): it is an `opaque` that no \
         source file of this build declared and that the native opaque audit does not \
         classify as a genuine implementation, so its value may be a stand-in for an \
         implementation Clean does not have (native-opaque-unaudited)."
    )]
    Unaudited {
        /// The refused constant.
        name: String,
        /// The declaration being built.
        root: String,
    },
}

/// Refuse to compile a reached constant whose value the native path cannot
/// vouch for. Returns `Ok(())` for a shimmed symbol (its value is never
/// compiled), for value-less opaques (they drop to extern and fail closed at
/// link), for an opaque a source file of this build declared, for a prelude
/// opaque the audit classifies [`OpaqueRuntime::Genuine`], and for every
/// definition the definition audit does not classify as a placeholder or as
/// Lean-divergent.
pub(crate) fn refuse_unfaithful_body(
    info: &ConstantInfo,
    root: &Name,
    source_opaques: &HashSet<Name>,
) -> Result<(), UnfaithfulOpaque> {
    if info.value.is_none() || is_primitive_denylisted(&mangle_name(&info.name)) {
        return Ok(());
    }
    let name = info.name.to_string();
    let placeholder = |entry: &OpaqueAuditEntry| UnfaithfulOpaque::Placeholder {
        name: name.clone(),
        root: root.to_string(),
        reason: entry.reason,
    };
    match info.kind {
        ConstantKind::Definition => match definition_audit_entry(&name) {
            Some(entry) if entry.runtime == OpaqueRuntime::Placeholder => Err(placeholder(entry)),
            Some(entry) if entry.runtime == OpaqueRuntime::LeanDivergent => {
                Err(UnfaithfulOpaque::LeanDivergent {
                    name,
                    root: root.to_string(),
                    reason: entry.reason,
                })
            }
            _ => Ok(()),
        },
        ConstantKind::Opaque if source_opaques.contains(&info.name) => Ok(()),
        ConstantKind::Opaque => match audit_entry(&name) {
            Some(entry) if entry.runtime == OpaqueRuntime::Genuine => Ok(()),
            Some(entry) => Err(placeholder(entry)),
            None => Err(UnfaithfulOpaque::Unaudited {
                name,
                root: root.to_string(),
            }),
        },
        _ => Ok(()),
    }
}

#[cfg(test)]
#[path = "native_opaque_audit_tests.rs"]
mod tests;

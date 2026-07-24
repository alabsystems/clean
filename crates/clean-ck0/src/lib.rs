// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean-ck0` — the **frozen decision-core seed** of the `ck2` kernel.
//!
//! This crate carries milestones **M0–M2** of the build spec
//! `designs/2026-06-16-ck2-kernel.md`:
//!
//! * **M0** — the seed layer: the private, smart-constructed trusted types
//!   (`Name`, `Level`, `BigNat`, `Term`/`ConstRef`/`ElimRef`), the untrusted
//!   boundary IR (`RawExpr`), the single validation chokepoint
//!   (`Term::validate`), and the two-valued [`Verdict`].
//! * **M1** — the decision core: `whnf`, `def_eq` (η, proof-irrelevance, Quot),
//!   `infer`/`check`/`infer_sort`, budget threading.
//! * **M2** — inductive admission + recursor derivation
//!   ([`inductive::add_inductive`]): structural-identity idempotency, strict
//!   positivity, the universe constraint, the subsingleton/large-elim gate, and
//!   kernel-checked recursor type + ι-rule derivation
//!   ([`recursor::build_recursor`]) for single, non-mutual, non-nested
//!   inductives. The cert path is M5+.
//! * **M3** — mutual + nested inductive admission. [`mutual::add_inductive_mutual`]
//!   admits a block of `N` inductives defined together and derives one recursor
//!   per type (`N` motives, minors over every block constructor, cross-type
//!   recursive fields). [`nested::add_inductive_nested`] compiles a nested
//!   occurrence (e.g. `RoseTree : List RoseTree -> RoseTree`) to a mutual block
//!   via the auxiliary construction. Every derived recursor type is
//!   kernel-checked; non-strictly-positive nesting is rejected. Single-inductive
//!   M2 behaviour is unchanged.
//!
//! # The two structural guarantees (design §3, §4.3)
//!
//! 1. **No `unsafe`, ever.** `#![forbid(unsafe_code)]` is *unconditional* — no
//!    `cfg_attr(not(kani))` escape hatch (design §3.2 / §11-R "flat unsafe").
//! 2. **No fixed-width integer *arithmetic* and no `as` casts outside the
//!    audited bignat module; and no `f64`/`f32` anywhere.** This makes the
//!    Incident-#2 (overflow / `from_f64` saturation) bug class a *syntactic*
//!    property of the crate rather than a guarded runtime check (design §4.3
//!    Incident #2). Enforced three ways:
//!      * `#![deny(clippy::arithmetic_side_effects)]` — flags fixed-width add/
//!        mul/sub/... that can overflow. De Bruijn `u32` indices are *compared*,
//!        never arithmetic'd into a value, so they do not trip this; the one
//!        place fixed-width arithmetic is genuinely needed (the `BigNat`
//!        small-value fast path) is confined to [`bignat`] and each site is
//!        documented and refinement-tested.
//!      * `#![deny(clippy::cast_possible_truncation)]` etc. — keep `as` casts
//!        honest; the audited casts live in [`bignat`] with `// AUDIT:` notes.
//!      * a CI grep helper, [`policy::POLICY`], plus the test
//!        `tests/no_float_no_unaudited_cast.rs`, which greps the crate source
//!        for `f64`/`f32` and for `as` casts outside `bignat.rs`.
//!
//! Every soundness-critical invariant of the seed is a property of a *private
//! type with a smart constructor*, established once at the chokepoint, never
//! re-validated ad hoc (design principle 2). Because the trusted types have
//! private fields, nothing outside this crate can fabricate an ill-formed
//! `Term`, a wrong-arity `ConstRef`, or a caller-authored eliminator level
//! vector.

#![forbid(unsafe_code)]
// --- Structural guarantee #2: fixed-width-arithmetic / cast discipline. ---
// These are crate-level `deny`s, on top of the workspace clippy gate. The
// audited exception module is `bignat`, which carries `#[allow(...)]` at each
// documented site (search `// AUDIT:` there).
#![deny(clippy::arithmetic_side_effects)]
#![deny(clippy::cast_possible_truncation)]
#![deny(clippy::cast_possible_wrap)]
#![deny(clippy::cast_sign_loss)]
#![deny(clippy::cast_precision_loss)]
// Defensive: no integer overflow even in checked-wrapping forms outside bignat.
#![deny(clippy::cast_lossless)]

pub mod bignat;
pub mod budget;
pub mod def_eq;
pub mod elim_analysis;
pub mod inductive;
pub(crate) mod inductive_params;
pub mod infer;
pub mod level;
pub mod minimal_env;
pub mod mutual;
pub mod name;
pub mod nested;
pub(crate) mod nested_replace;
pub mod policy;
pub(crate) mod positivity;
pub mod rawexpr;
pub mod recursor;
pub(crate) mod recursor_build;
pub(crate) mod recursor_mutual;
pub(crate) mod recursor_mutual_minor;
pub(crate) mod recursor_mutual_rhs;
pub(crate) mod recursor_rules;
pub(crate) mod staging_env;
pub mod term;
pub mod term_ops;
pub mod validate;
pub mod verdict;
pub mod whnf;

pub use bignat::BigNat;
pub use budget::{Budget, BudgetError};
pub use def_eq::is_def_eq;
pub use inductive::{
    add_inductive, AdmitError, AdmittedInductive, Constructor, InductiveDecl, MutableEnv,
};
pub use infer::{check, infer, infer_in_context, infer_sort, infer_sort_in_context, InferError};
pub use level::{Level, LevelError};
pub use minimal_env::MinimalEnv;
pub use mutual::{add_inductive_mutual, AdmittedMutual, MutableMutualEnv, MutualBlock};
pub use name::Name;
pub use nested::{add_inductive_nested, NestedError};
pub use rawexpr::{RawExpr, RawLevel, RawLit};
pub use recursor::{IotaRule, RecursorData};
pub use term::{ConstRef, ElimRef, Term, TermError};
pub use validate::{
    ConstDef, ConstructorArity, Env, QuotKind, RecursorShape, StructureInfo, Transparency,
    ValidateError, MAX_VALIDATE_DEPTH,
};
pub use verdict::{CertVerdict, ConstId, Reason, Verdict};
pub use whnf::whnf;

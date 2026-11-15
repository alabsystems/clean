// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean-ck0` — the **decision-core seed** of the `ck2` kernel.
//!
//! The design (`designs/2026-06-16-ck2-kernel.md`) calls this seed frozen, and
//! `genesis/ck0/MANIFEST.txt` pins it by checksum. That pin is stale: the
//! source has moved since it was minted (on 2026-11-12 the checksum step of
//! `genesis/ck0/verify.sh` failed most of the listed files, and no gate runs
//! it). Re-pinning the seed to current source is unit Q6 of the plan named
//! below; re-run that check, and read Q6's row, before calling the pin current.
//!
//! # Role in the kernel self-proof
//!
//! The route of record is `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`
//! (it amends `docs/DECISIONS.md` R29). There the trust root is, by design, to
//! be `kcheck`, a checker defined in Lean; this crate is not that checker and
//! is not proved. Its role is to be the member of the re-check quorum that is
//! built by stock rustc, which is a property of the run that builds it and not
//! of this source.
//!
//! With feature `export`, the independent reader and `ck0-replay` command check
//! bounded lean4export 3.1.0 bytes: single/mutual/nested inductives with derived
//! recursors, quotients, canonical literals and licensed native operations.
//! The crate README records measured qualification and availability limits.
//! Counted quorum votes also require the adopted dialect and target/statement/
//! axiom-closure contract. RawExpr remains the untrusted term boundary.
//!
//! # Who links it
//!
//! Inside Clean's workspace no crate depends on this one outside
//! `[dev-dependencies]`: the callers are tests of `clean-kernel` and
//! `clean-olean`. Outside the workspace that is not so. Read on 2026-11-12
//! from the sibling checkouts' `origin/main`:
//!
//! * ty's `crates/tla-check` has an optional production dependency on this
//!   crate, enabled by its feature `clean-cic`, which is among that crate's
//!   default features. Its non-test module `ck0_bridge` translates
//!   `clean_kernel::Expr` into `RawExpr` and asks this crate to check the
//!   term; a rejection of a term `clean-kernel` accepted fails ty's
//!   certification closed.
//! * Trust's `crates/trust-spec-temporal` links `tla-check` under
//!   `[dependencies]` with `clean-cic` on, patches `clean-ck0` to its
//!   `first-party/clean` checkout, and its manifest says both Clean checkers
//!   are part of that authority closure.
//!
//! So this crate already runs as production code inside an authority closure
//! in Trust, as a second checker that can refuse, over a translation and
//! with the stale pin above. The finding and what it changes for the plan's
//! units P1 and Q6 are in `docs/DECISIONS.md` (2026-11-12, "`clean-ck0` is
//! linked in production outside this workspace"). Those manifests move; read
//! them again before relying on this paragraph.
//!
//! # What the crate carries
//!
//! This crate carries milestones **M0–M3** of the build spec
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
//!   (`recursor::build_recursor`) for single, non-mutual, non-nested
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
#[cfg(feature = "export")]
pub mod export;
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
pub mod term_dag;
mod term_ops;
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
pub use level::{Level, LevelError, MAX_LEVEL_GEQ_WORK, MAX_LEVEL_SIZE};
pub use minimal_env::MinimalEnv;
pub use mutual::{add_inductive_mutual, AdmittedMutual, MutableMutualEnv, MutualBlock};
pub use name::Name;
pub use nested::{add_inductive_nested, NestedError, MAX_AUX_SIZE};
pub use rawexpr::{RawExpr, RawLevel, RawLit};
pub use recursor::{IotaRule, RecursorData};
pub use term::{ConstRef, ElimRef, Term, TermError};
pub use validate::{
    ConstDef, ConstructorArity, Env, QuotKind, RecursorShape, StructureInfo, Transparency,
    ValidateError, WrittenLevel, MAX_VALIDATE_DEPTH,
};
pub use verdict::{CertVerdict, ConstId, Reason, Verdict};
pub use whnf::whnf;

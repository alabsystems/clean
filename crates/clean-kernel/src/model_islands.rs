// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The self-verification model, embedded as Clean islands.
//!
//! Embed memo [`designs/2026-08-28-embedding-the-kernel-model.md`], owner ruling 5
//! taken for IN-PLACE ISLANDS. Each `clean mod` below is Trust's OUT-OF-LINE
//! island form: the compiler loads the named `.clean` file from disk BYTE FOR
//! BYTE at expansion time (`rustc_expand::module::load_clean_unit`, parsed by
//! `rustc_parse`'s `parse_clean_mod_unit`), parses it with the REAL Clean
//! parser, and registers every declaration through `add_decl` — so the CIC
//! kernel type-checks the model during this crate's Rust build, a rejected unit
//! fails that build, and diagnostics point into the `.clean` file itself.
//!
//! The out-of-line form is what makes this ONE source of truth: the unit files
//! under `crates/clean-verify/spec/` are the model, and nothing is copied,
//! rendered or regenerated to put them here. (The inline `clean { … }` form
//! would have required a transformed second copy, because an inline island is
//! delimited by a Rust token tree and the units contain 40 `→`, 114 backticks
//! and apostrophes that do not lex as Rust.)
//!
//! # WHICH kernel checks these units
//!
//! Not this crate's. The checker is baked into the Trust compiler at ITS build
//! time, from Trust's `first-party/clean` submodule — pinned at `d93b2fbb9`
//! (2026-08-20), which is **1,291 commits behind this repo's `main`, with 145
//! `crates/clean-kernel` files changed since**. So "the CIC kernel type-checks
//! the model during this crate's Rust build" is true of a kernel from
//! 2026-08-20, and a change to the kernel in THIS tree does not change what
//! checks these units until Trust re-pins its submodule and a new stage2 is
//! built. That is a real limit on what a green here means, and it is why the
//! gate reports the compiler's own verdict rather than claiming anything about
//! the kernel beside it.
//!
//! # What this establishes, and what it does not
//!
//! TRUE, and gated: these declarations kernel-check, as written, inside the Rust
//! build, over the COMPILER PRELUDE's foundation.
//!
//! NOT established: that the model the `clean-verify` theorems are about is what
//! checks here. Those theorems are stated over the spec's own foundation, built
//! on an EMPTY environment with its own `Nat`/`Eq`/`ListType`;
//! `expr_model_core` references `Nat` 37 times and `Nat` is prelude-owned, so
//! these units elaborate against the prelude's. Closing that distance is the
//! memo's FOUNDATION TRANSPORT, which is open.
//!
//! # Why only three units
//!
//! The island environment has a prelude, and the kernel's `add_inductive`
//! idempotence guard SILENTLY accepts a re-declaration that names a prelude name
//! with a SUBSET of its constructors — it reports the name as registered while
//! registering nothing that was written. Measured 2026-09-12: exactly three
//! model names are prelude-owned (`Nat`, `Eq`, `Empty`), so a unit declaring one
//! of them reports a kernel-checked green for the PRELUDE's declaration.
//! `scripts/model_islands.py --verify` refuses that, and only units whose every
//! name is free are listed here:
//!
//! | excluded unit | why |
//! |---|---|
//! | `foundation_nat` | `Nat` aliased; `Nat.add`/`Nat.pred`/`Nat.sub` collide outright |
//! | `foundation_eq` | `Eq` aliased — the whole unit would be a false green |
//! | `foundation_empty_and` | `AndType` is free, but its unit-mate `Empty` is prelude-owned and the compiler refuses its re-declaration (2026-10-28) |
//! | `expr_model_spine` | island elaboration fails on `kapp_fn`/`kapp_arg_count` |
//!
//! Evidence: `reports/clean-island-embedding-feasibility-2026-09-12.md`.

// The six declarations the model shares with the ambient environment -- `Nat`,
// `Nat.add`, `Nat.pred`, `Nat.sub`, `Eq`, `Empty` -- cannot be re-declared here:
// the prelude owns them, an `inductive` re-declaration naming a subset of its
// constructors is SILENTLY accepted, and a `def` re-declaration is refused. So
// this unit states the model's DEFINING EQUATIONS for them instead, each held by
// `Eq.refl` so the kernel must decide it by computation. In the spec's own
// environment these are trivially true; here they are a real check, and they
// fail unless the prelude computes exactly as the model does.
// registers: fa_nat_zero, fa_nat_succ, fa_nat_add_zero, fa_nat_add_succ,
//            fa_nat_pred_zero, fa_nat_pred_succ, fa_nat_sub_zero,
//            fa_nat_sub_succ, fa_eq_refl, fa_empty_elim
#[path = "../../clean-verify/spec/foundation_agreement.clean"]
clean mod foundation_agreement;

// registers: Name, Level, ListType, KExpr, lift_bvar_at, lift_at, lift,
//            instantiate_bvar_geq, instantiate_bvar_at, instantiate_at, instantiate
#[path = "../../clean-verify/spec/expr_model_core.clean"]
clean mod expr_model_core;

// The spine layer. It MUST be loaded beside `expr_model_core`: on its own, `KExpr`
// is not in the environment and the elaborator's Lean-compatible auto-bound-implicit
// rule silently turns the binder type into an implicit `{KExpr : Sort u}`, whose
// `match` then has no nameable type constructor ("cannot extract type name from
// opaque type variable"). That is a property of compiling the unit ALONE, not a
// defect in either front end -- measured both ways.
// registers: kapp_fn, kapp_arg_count, is_const_app
#[path = "../../clean-verify/spec/expr_model_spine.clean"]
clean mod expr_model_spine;

// registers: Lt, Le
#[path = "../../clean-verify/spec/foundation_order.clean"]
clean mod foundation_order;

// registers: ProdType
#[path = "../../clean-verify/spec/foundation_prod.clean"]
clean mod foundation_prod;

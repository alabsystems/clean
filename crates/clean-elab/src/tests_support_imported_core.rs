// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test support: register Lean 4.8.0 `Init` constants in an environment the
//! way the `.olean` importer does — straight into the kernel environment —
//! for fixtures that exercise a tactic on an environment that imported
//! `Init`.
//!
//! A fixture may not DECLARE such a constant from source: it is a Lean core
//! name, which Lean refuses ("already declared") and so does Clean
//! (`crate::lean_core_names`). Fixtures used to write `axiom dif_pos …` and
//! the like as a stand-in for `import Init`; that stand-in is now this
//! registration. (An `import Init` integration test was tried and retired: a
//! DEBUG build imports Init in over thirty minutes at ten gigabytes.)

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::{Declaration, Environment, Name};
use clean_parser::parse_file;

/// Lean 4.8.0 `Init.Core`: `dif_pos`/`dif_neg` (statements as `#check`
/// prints them).
pub(crate) const DIF_POS_NEG: &[(&str, &str)] = &[
    (
        "dif_pos",
        "{c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : \
         @dite α c h t e = t hc",
    ),
    (
        "dif_neg",
        "{c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : \
         @dite α c h t e = e hnc",
    ),
];

/// Lean 4.8.0 `Init.SimpLemmas`: `forall_congr`.
pub(crate) const FORALL_CONGR: &[(&str, &str)] = &[(
    "forall_congr",
    "{α : Sort u} {p q : α → Prop} (h : ∀ a, p a = q a) : (∀ a, p a) = (∀ a, q a)",
)];

/// Register each `(name, signature)` in `env` as an imported axiom: the
/// signature is elaborated in a scratch copy of `env` under a placeholder
/// name, and its type registered under `name` through the kernel.
///
/// A name the environment already declares is left alone — its declared
/// type must then be the imported signature's, which is checked here. Since
/// G39 (ledger (109)) the default prelude carries `forall_congr` itself, as a
/// kernel-checked theorem with Lean's statement.
pub(crate) fn import_core_constants(env: &mut Environment, constants: &[(&str, &str)]) {
    let mut scratch = env.clone();
    for (index, (name, signature)) in constants.iter().enumerate() {
        let placeholder = format!("importedCoreConstant{index}");
        let decls = parse_file(&format!("axiom {placeholder} {signature}\n"))
            .unwrap_or_else(|e| panic!("`{name}` signature must parse: {e:?}"));
        for decl in &decls {
            elaborate_decl_and_register_with_warning(&mut scratch, decl)
                .unwrap_or_else(|e| panic!("`{name}` signature must elaborate: {e:?}"));
        }
        let info = scratch
            .get_const(&Name::from_string(&placeholder))
            .unwrap_or_else(|| panic!("`{name}` signature must register"));
        if let Some(present) = env.get_const(&Name::from_string(name)) {
            assert!(
                present.type_ == info.type_ && present.level_params == info.level_params,
                "`{name}` is already declared with a different statement than the imported one"
            );
            continue;
        }
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
        })
        .unwrap_or_else(|e| panic!("import `{name}`: {e:?}"));
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The complete-signature test shared by the two surface decision-tree
//! builders: `compile_pattern_matrix` (equation-form definitions,
//! `infer/elab_decl_value.rs`) and `build_column_split_surface`
//! (constructor-field splits of `match`, `infer/elab_match/ctor_order.rs`).
//!
//! Both split a column on the constructor heads its rows name and, for rows
//! whose head is a binder, emit a trailing DEFAULT arm (Maranget's default
//! matrix) so the constructors no row names are still covered. When the heads
//! already name every constructor of the column's inductive, no value reaches
//! that default: every binder row has been spliced into each constructor arm.
//! Compiling it anyway is not harmless — its rows are only the binder rows, so
//! their remaining columns can form a PARTIAL match of their own
//! (`| _, .top => … | .top, _ => … | .interval .., .interval .. => …` leaves
//! `match y with | .top => …` under the default of the first column), and the
//! whole definition was refused. Lean 4.8.0's `processConstructor`
//! (`src/Lean/Meta/Match/Match.lean`) splits on every constructor of the
//! inductive and has no default arm at all.

use clean_kernel::name::Name;
use clean_kernel::Environment;

/// The inductive whose constructors `ctors` name ALL of, when they are
/// constructors of one inductive (Maranget's complete signature). `None` when
/// some name is not a constructor the environment knows, when they span two
/// inductives, when some constructor of the inductive is missing, or when
/// `ctors` is empty — each the conservative answer, which keeps the default
/// arm.
pub(in crate::infer) fn complete_signature_inductive<'n>(
    env: &Environment,
    ctors: impl IntoIterator<Item = &'n Name>,
) -> Option<Name> {
    let mut inductive: Option<&Name> = None;
    let mut named: Vec<&Name> = Vec::new();
    for name in ctors {
        let ctor = env.get_constructor(name)?;
        match inductive {
            None => inductive = Some(&ctor.inductive_name),
            Some(ind) if *ind == ctor.inductive_name => {}
            Some(_) => return None,
        }
        named.push(name);
    }
    let info = env.get_inductive(inductive?)?;
    info.constructor_names
        .iter()
        .all(|ctor| named.contains(&ctor))
        .then(|| info.name.clone())
}

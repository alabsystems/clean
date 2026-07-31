// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **pattern library**: one submodule per Isabelle fragment, each mapping a
//! set of constants to a faithful Lean rendering (or a first-class decline). The
//! [`dispatch`] hub routes an application head + argument list to the first
//! fragment that claims the constant; a head no fragment claims falls through to
//! [`super::types::Unsupported::UnknownConst`] in [`super::term`].
//!
//! Adding a fragment is a localized change: implement `try_translate` and add it
//! to the [`dispatch`] chain. The faithfulness rule is enforced fragment-local —
//! every renderer either produces the exact Lean term or returns an
//! [`Unsupported`] the guard proves (never a plausible guess).

pub(super) mod arithmetic;
pub(super) mod binders;
pub(super) mod connectives;
pub(super) mod lists;
pub(super) mod orders;
pub(super) mod sets;
pub(super) mod sublists;

use super::super::isabelle_pure::{IsaTerm, IsaType};
use super::term::translate_term;
use super::types::{LeanTerm, Unsupported};

/// Route an application head `n` (with its own constant type `head_ty`, applied
/// to `args`) to the pattern library.
///
/// Returns `None` iff **no** fragment recognizes `n` (the caller reports
/// [`Unsupported::UnknownConst`]); `Some(Ok)` for a faithful rendering; and
/// `Some(Err)` when a fragment recognizes the constant but a guard declines
/// (e.g. a polymorphic order/lattice) — the honest "recognized-but-unfaithful"
/// signal.
///
/// `head_ty` is the head `Const`'s already-instantiated type; the set fragment
/// consumes it to guard the **nullary** lattice constants (`bot`/`top`), which
/// carry no argument to inspect. Every other fragment guards on its arguments.
pub(super) fn dispatch(
    n: &str,
    head_ty: &IsaType,
    args: &[&IsaTerm],
) -> Option<Result<LeanTerm, Unsupported>> {
    binders::try_translate(n, args)
        .or_else(|| connectives::try_translate(n, args))
        .or_else(|| arithmetic::try_translate(n, args))
        .or_else(|| lists::try_translate(n, args))
        .or_else(|| sets::try_translate(n, head_ty, args))
        .or_else(|| orders::try_translate(n, args))
        .or_else(|| sublists::try_translate(n, args))
}

/// Build a named prefix application `head arg₁ … argₙ` (e.g. `Set.image f A`,
/// `Set.InjOn f A`, `List.zip xs ys`). Requires exactly `arity` arguments; the
/// render layer parenthesizes each argument that is itself an application/infix.
pub(super) fn prefix_app(
    head: &'static str,
    arity: usize,
    args: &[&IsaTerm],
) -> Result<LeanTerm, Unsupported> {
    if args.len() != arity {
        return Err(Unsupported::PartialApplication(head.to_string()));
    }
    let rendered: Result<Vec<LeanTerm>, Unsupported> =
        args.iter().map(|a| translate_term(a)).collect();
    Ok(LeanTerm::App {
        head: head.to_string(),
        args: rendered?,
    })
}

/// Build a binary infix node from a 2-argument spine, declining a partial
/// application. Shared by every fragment's binary operators.
pub(super) fn binary_infix(
    const_name: &str,
    op: &'static str,
    prec: u8,
    args: &[&IsaTerm],
) -> Result<LeanTerm, Unsupported> {
    let [l, r] = args else {
        return Err(Unsupported::PartialApplication(const_name.to_string()));
    };
    Ok(LeanTerm::infix(
        op,
        prec,
        translate_term(l)?,
        translate_term(r)?,
    ))
}

/// Build a dot-notation method node whose **receiver is the last argument** and
/// whose method arguments are the leading arguments (the Isabelle
/// prefix-with-object-last convention: `map f xs` → `xs.map f`). Requires exactly
/// `arity` arguments.
pub(super) fn method_object_last(
    const_name: &str,
    method: &'static str,
    arity: usize,
    args: &[&IsaTerm],
) -> Result<LeanTerm, Unsupported> {
    if args.len() != arity || args.is_empty() {
        return Err(Unsupported::PartialApplication(const_name.to_string()));
    }
    let (method_args, recv) = args.split_at(args.len() - 1);
    let recv = translate_term(recv[0])?;
    let rendered: Result<Vec<LeanTerm>, Unsupported> =
        method_args.iter().map(|a| translate_term(a)).collect();
    Ok(LeanTerm::method(recv, method, rendered?))
}

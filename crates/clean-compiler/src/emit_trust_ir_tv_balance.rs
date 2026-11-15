// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The STRUCTURAL half of the TV mint gate ([`super`]): the Fragment-4
//! alloc/release balance, a claim the value equation cannot carry. The
//! minter calls it on every in-fragment body before the kernel judgment's
//! certificate is attached; a violation is a REFUSAL.

use std::collections::BTreeMap;

use trust_ir::inst::Inst;
use trust_ir::Function;

/// STRUCTURAL alloc/release balance check (Fragment-4, honesty note 1),
/// mirrored by trust-ir's `clean_backend_tv` re-checker
/// (`trust_ir_build::validate`, `alloc_release_balance`). A Fragment-4 cell is
/// a reference-counted `CleanHeap` cell, released by the `Release` that takes
/// its count to zero and never by `Dealloc` (trust-ir SPEC "A
/// reference-counted cell is released by `Release`, never by `Dealloc`"). So:
///
/// * every `HeapAlloc` result must be `Release`d EXACTLY ONCE (the count is 1
///   in the fragment, so that `Release` frees it);
/// * a `Dealloc` of an allocation base is REFUSED — undefined behaviour under
///   the SPEC rule, a wrong emission;
/// * a `Release` of any other value is neither counted nor refused here.
///   Inside a Fragment-4 segment the walker already keeps it out of the
///   fragment. A Fragment-5 `Release` (a `dec` of a call result) is balanced
///   by the walker itself — `clean_reflect::denote`'s `f5_ownership_balance`,
///   which runs on every admitted Fragment-5 body, kernel-judged or not, and
///   refuses a use after free, a count underflow or a leak as a wrong
///   emission before this gate is reached.
///
/// The value equation cannot observe the release, so this is the emit gate's
/// claim, not the kernel's — a violation on an otherwise in-fragment function
/// is a detected wrong-code emission (REFUSED). Vacuous for heap-free
/// (Fragment-2/3/5) functions.
pub(super) fn alloc_release_balance(func: &Function) -> Result<(), String> {
    let mut release_count: BTreeMap<u32, usize> = BTreeMap::new();
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::HeapAlloc { .. } = &node.inst {
                if let [r] = node.results.as_slice() {
                    release_count.insert(r.index(), 0);
                }
            }
        }
    }
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::Release { ptr } = &node.inst {
                // Only a Release of a HeapAlloc result is counted.
                if let Some(c) = release_count.get_mut(&ptr.index()) {
                    *c += 1;
                }
            }
            if let Inst::Dealloc { ptr } = &node.inst {
                if release_count.contains_key(&ptr.index()) {
                    return Err(format!(
                        "alloc/release balance: allocation %{} is freed by Dealloc, which is \
                         undefined behaviour on a reference-counted cell (it is released by \
                         Release) — a wrong emission",
                        ptr.index()
                    ));
                }
            }
        }
    }
    for (alloc, count) in &release_count {
        match count {
            1 => {}
            0 => {
                return Err(format!(
                    "alloc/release balance: allocation %{alloc} has no Release (dropped \
                     Release — a leak the value equation cannot see)"
                ));
            }
            n => {
                return Err(format!(
                    "alloc/release balance: allocation %{alloc} has {n} Releases (doubled \
                     Release — a double-free the value equation cannot see)"
                ));
            }
        }
    }
    Ok(())
}

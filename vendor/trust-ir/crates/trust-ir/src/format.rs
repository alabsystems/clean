// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical TrustIr text pretty-printer for diff stability (issue #62).
//!
//! [`canonical`] returns the canonical text form of a [`Module`]: the
//! deterministic, idempotent, diff-stable rendering that the `trust-ir fmt`
//! CLI emits.
//!
//! # What "canonical" means
//!
//! The default `impl fmt::Display for Module` in `display.rs` is optimized
//! for human readability and preserves insertion order. Two semantically
//! equivalent modules built by different frontends (e.g., `tRust` vs.
//! `ty` emitting the same source) can print differently because:
//!
//! - SSA value numbers (`%42`) reflect the builder's internal arena layout,
//!   not the logical use position.
//! - Adjacent declaration spacing is not fully stable (lone blank lines
//!   vs. double blanks depend on whether the previous item wrote a
//!   trailing newline).
//! - `Constant::Float(42.0)` could historically print as `42`, which the
//!   parser then reads back as `Constant::Int(42)` (#45, #47 — already
//!   fixed in `display::write_constant_float`).
//!
//! [`canonical`] eliminates all of these by:
//!
//! 1. **Dense SSA renumbering.** Per function, rewrite every `ValueId` to
//!    a dense `0..N` index: first block-parameter definitions in block-id
//!    order, then instruction results in original instruction order. All
//!    operand references are remapped via the same table.
//! 2. **Deterministic decl order.** Module-level tables (`structs`,
//!    `enums`, `records`, `func_types`, `closure_types`, `globals`,
//!    `functions`, `proof_obligations`, `proof_certificates`) are already
//!    stored in id order (`add_*` uses `len()` as the new id). Blocks are
//!    emitted in `block.id` order within each function.
//! 3. **Stable whitespace.** Exactly one blank line between functions;
//!    single newline between top-level decls; no trailing blank lines.
//! 4. **Float canonical tokens.** `Constant::Float` emits via `{:?}`
//!    (shortest round-tripping decimal, always contains `.` or `e`) —
//!    inherited from the existing `write_constant_float` helper.
//!
//! # Idempotency
//!
//! `canonical(canonical_parsed(m)) == canonical(m)` (see the
//! `idempotent_*` snapshot tests). A parsed canonical output must
//! re-canonicalize to the same bytes.
//!
//! # Semantic preservation
//!
//! Canonicalization is purely syntactic. `validate_module(&canonicalize(m))`
//! produces the same diagnostic set as `validate_module(&m)` (modulo the
//! SSA renumbering; validation is SSA-name-invariant). The helper
//! [`canonicalize`] returns the rewritten [`Module`] for callers who want
//! both the canonical module and its string form.

// The authoritative per-instruction SSA operand-remap lives in `mem2reg`
// (always compiled), so the alloca-promotion pass can reuse it without
// pulling in the `fmt` feature. Canonicalization reuses the same walker here.
use crate::mem2reg::rewrite_node;
use crate::value::ValueId;
use crate::{Function, Module};
use std::collections::HashMap;

/// Render `module` in canonical TrustIr text form.
///
/// This is the string the `trust-ir fmt` CLI emits. See the module-level
/// documentation for the full definition of "canonical".
///
/// Guaranteed to be idempotent: `canonical(parse(canonical(m))) ==
/// canonical(m)` for every well-formed `m`, when the `parser` feature is
/// enabled.
pub fn canonical(module: &Module) -> String {
    let canon = canonicalize(module);
    format!("{canon}")
}

/// Return a new [`Module`] whose SSA values have been renumbered to a
/// dense canonical 0..N per function.
///
/// The returned in-memory module preserves every field unless canonicalization
/// actually rewrites that function. A rewritten function loses
/// [`Function::source_provenance`]: an ordinary syntactic transform is not
/// authorized to re-seal compiler source authority for a changed artifact.
/// Its canonical text can be fed back through the parser when `parser` is enabled, but the text
/// surface intentionally omits v31 enum field names and concrete layout
/// descriptors; use binary or serde when those producer facts must survive.
///
/// Callers that want only the text form should use [`canonical`]
/// directly.
pub fn canonicalize(module: &Module) -> Module {
    let mut out = module.clone();
    for func in &mut out.functions {
        canonicalize_function(func);
    }
    out
}

/// Build the per-function dense SSA remap table.
///
/// Visit block parameters first (in block-id order), then instruction
/// results (in original instruction order per block). Every `ValueId`
/// defined by the function receives a fresh dense index in `0..N`.
fn build_value_map(func: &Function) -> HashMap<ValueId, ValueId> {
    let mut map = HashMap::new();
    let mut next: u32 = 0;

    // Blocks are already canonical if emitted in block.id order; the
    // walker below enforces that order by sorting a temporary vector of
    // block indices. We do NOT mutate the block vector here — the Display
    // impl iterates `func.blocks` directly, so the caller must also sort
    // blocks (see `canonicalize_function`).
    let mut block_indices: Vec<usize> = (0..func.blocks.len()).collect();
    block_indices.sort_by_key(|&i| func.blocks[i].id.index());

    // Pass 1: block parameters in block-id order.
    for &bi in &block_indices {
        for (val, _ty) in &func.blocks[bi].params {
            map.entry(*val).or_insert_with(|| {
                let id = ValueId::new(next);
                next += 1;
                id
            });
        }
    }

    // Pass 2: instruction results in original block-id-then-source order.
    for &bi in &block_indices {
        for node in &func.blocks[bi].body {
            for r in &node.results {
                map.entry(*r).or_insert_with(|| {
                    let id = ValueId::new(next);
                    next += 1;
                    id
                });
            }
        }
    }

    map
}

/// Render a single function in canonical text form: canonicalize a clone
/// (dense SSA renumbering, stable block order, trimmed trailing empty param
/// attrs) and print it via the `Display` impl.
///
/// This is the per-function slice of [`canonical`], used by
/// [`crate::Module::obligation_digest`] as its arena-order/value-renumbering
/// insensitive function-content encoding. NOTE: the rendering still contains
/// the function's `functy.N` signature index — module-level *type-table*
/// renumbering is not normalized here (nor by [`canonical`], which prints
/// tables in id order).
pub(crate) fn canonical_function(func: &Function) -> String {
    let mut canon = func.clone();
    canonicalize_function(&mut canon);
    format!("{canon}")
}

/// Canonicalize a function in place: sort blocks by `block.id`, then
/// rewrite every `ValueId` that appears in the function (definitions and
/// uses) via the dense remap table.
fn canonicalize_function(func: &mut Function) {
    // Temporarily remove proof-bearing source provenance while deciding
    // whether this pass changes the function. If it does, fail closed by
    // leaving the carrier absent. An already-canonical function can retain its
    // byte-identical carrier.
    let source_provenance = func.source_provenance.take();
    let before = func.clone();

    // 0. Trim trailing empty per-parameter attribute slots. The text printer
    //    emits `#param_attrs {i}:` only for non-empty entries by index, and the
    //    parser reconstructs the vector up to the highest non-empty index — so a
    //    trailing `ParamAttrs::default()` slot cannot survive a text round-trip.
    //    Normalizing it away here keeps the canonical form equal to what text
    //    print→parse produces (trailing empties are semantically inert).
    while func.attrs.params.last().is_some_and(|pa| pa.is_empty()) {
        func.attrs.params.pop();
    }

    // 1. Stable block order (by block.id).
    func.blocks.sort_by_key(|b| b.id.index());

    // 2. Build the dense SSA remap.
    let map = build_value_map(func);

    // 3. Rewrite every ValueId occurrence in the function.
    for block in &mut func.blocks {
        for (val, _ty) in &mut block.params {
            *val = *map.get(val).unwrap_or(val);
        }
        for node in &mut block.body {
            rewrite_node(node, &map);
        }
    }

    // Debug names refer to the same SSA namespace as parameters, results, and
    // operands. Leaving this side table sparse while rewriting the body would
    // silently attach names to the wrong canonical values.
    if let Some(names) = &mut func.value_names {
        for (value, _) in names {
            *value = *map.get(value).unwrap_or(value);
        }
    }

    if *func == before {
        func.source_provenance = source_provenance;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Block;
    use crate::inst::{BinOp, ICmpOp, Inst};
    use crate::node::InstrNode;
    use crate::proof::ProofAnnotation;
    use crate::ty::{FuncTy, Ty};
    use crate::value::{BlockId, FuncId};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    /// `fn add(i64 %0, i64 %1) -> i64 { %2 = add %0, %1; ret %2 }`
    /// But with sparse SSA numbering: %17, %19, %23.
    fn sparse_add_module() -> Module {
        let mut module = Module::new("sparse_add");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "add", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(17), Ty::I64));
        block.params.push((v(19), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(17),
                rhs: v(19),
            })
            .with_result(v(23)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![v(23)],
        }));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn canonicalize_renumbers_ssa_densely() {
        let m = sparse_add_module();
        let c = canonicalize(&m);
        let block = &c.functions[0].blocks[0];
        // Params are %0, %1 after canonicalization.
        assert_eq!(block.params[0].0, v(0));
        assert_eq!(block.params[1].0, v(1));
        // BinOp result is %2.
        assert_eq!(block.body[0].results[0], v(2));
        // ret references %2.
        match &block.body[1].inst {
            Inst::Return { values } => assert_eq!(values[0], v(2)),
            _ => panic!("expected Return"),
        }
    }

    #[test]
    fn canonicalize_invalidates_only_when_it_rewrites_source_bound_body() {
        use crate::SourceProvenance;
        use crate::proof::ProofDigest;

        let carrier = || {
            SourceProvenance::new(
                ProofDigest::sha256([1; 32]),
                ProofDigest::sha256([2; 32]),
                Vec::new(),
            )
        };
        let mut sparse = sparse_add_module();
        sparse.functions[0].source_provenance = Some(carrier());
        let dense = canonicalize(&sparse);
        assert!(
            dense.functions[0].source_provenance.is_none(),
            "SSA renumbering must invalidate compiler source authority"
        );

        let mut already_dense = dense;
        already_dense.functions[0].source_provenance = Some(carrier());
        let unchanged = canonicalize(&already_dense);
        assert_eq!(
            unchanged.functions[0].source_provenance, already_dense.functions[0].source_provenance,
            "an actually byte-identical canonicalization may preserve the carrier"
        );
    }

    #[test]
    fn canonicalize_renumbers_value_name_side_table_with_body() {
        let mut m = sparse_add_module();
        m.functions[0].value_names = Some(vec![
            (v(17), "lhs".to_string()),
            (v(19), "rhs".to_string()),
            (v(23), "sum".to_string()),
        ]);

        let c = canonicalize(&m);
        assert_eq!(
            c.functions[0].value_names.as_deref(),
            Some(
                &[
                    (v(0), "lhs".to_string()),
                    (v(1), "rhs".to_string()),
                    (v(2), "sum".to_string()),
                ][..]
            )
        );
    }

    #[test]
    fn canonicalize_trims_trailing_empty_param_attrs() {
        use crate::ParamAttrs;
        // A function whose attrs.params is [non-empty, default]: the trailing
        // default slot cannot survive a text round-trip (Display emits only
        // non-empty entries by index), so canonicalize must drop it.
        let mut m = Module::new("trim");
        let ft = m.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::Ptr));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        func.attrs.params = vec![
            ParamAttrs {
                nonnull: true,
                ..Default::default()
            },
            ParamAttrs::default(), // trailing empty — should be trimmed
        ];
        m.add_function(func);

        let c = canonicalize(&m);
        assert_eq!(
            c.functions[0].attrs.params.len(),
            1,
            "trailing empty ParamAttrs slot must be trimmed"
        );
        assert!(c.functions[0].attrs.params[0].nonnull);
        // Idempotent: a second pass changes nothing.
        let c2 = canonicalize(&c);
        assert_eq!(c.functions[0].attrs.params, c2.functions[0].attrs.params);
    }

    #[test]
    fn canonical_is_idempotent_on_clean_input() {
        let m = sparse_add_module();
        let once = canonical(&m);
        // Round 2: canonicalize the already-canonical module.
        let c = canonicalize(&m);
        let twice = canonical(&c);
        assert_eq!(once, twice, "canonical must be idempotent");
    }

    #[test]
    fn canonical_sparse_and_dense_produce_same_text() {
        // Dense version of the same function: params %0, %1, result %2.
        let mut dense = Module::new("sparse_add");
        let ft = dense.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "add", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));
        block.params.push((v(1), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        dense.add_function(func);

        let sparse = sparse_add_module();
        assert_eq!(canonical(&sparse), canonical(&dense));
    }

    #[test]
    fn canonical_sorts_blocks_by_id() {
        let mut module = Module::new("blocks");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));

        // Push blocks out of order: b2 before b0 before b1.
        let mut b2 = Block::new(b(2));
        b2.params.push((v(100), Ty::I32));
        b2.body.push(InstrNode::new(Inst::Return {
            values: vec![v(100)],
        }));

        let mut b0 = Block::new(b(0));
        b0.params.push((v(200), Ty::I32));
        b0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(200)],
        }));

        let mut b1 = Block::new(b(1));
        b1.params.push((v(300), Ty::I32));
        b1.body.push(InstrNode::new(Inst::Br {
            target: b(2),
            args: vec![v(300)],
        }));

        func.blocks.push(b2);
        func.blocks.push(b0);
        func.blocks.push(b1);
        module.add_function(func);

        let c = canonicalize(&module);
        let ids: Vec<u32> = c.functions[0].blocks.iter().map(|b| b.id.index()).collect();
        assert_eq!(ids, vec![0, 1, 2], "blocks must be sorted by id");
    }

    #[test]
    fn canonical_preserves_proof_annotations() {
        let mut module = Module::new("proofs");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::Bool],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "eq", ft, b(0));
        func.proofs.push(ProofAnnotation::Pure);
        func.proofs.push(ProofAnnotation::Deterministic);
        let mut block = Block::new(b(0));
        block.params.push((v(10), Ty::I32));
        block.params.push((v(11), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(12))
            .with_proof(ProofAnnotation::Pure),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![v(12)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let text = canonical(&module);
        assert!(text.contains("; #proof: pure"), "want #proof annotation");
        assert!(
            text.contains("%2 = icmp eq i32 %0, %1"),
            "params renumbered to %0, %1; result to %2"
        );
    }

    #[cfg(feature = "parser")]
    #[test]
    fn canonical_fmt_parse_fmt_is_fixed_point() {
        use crate::parser::parse_module;
        let m = sparse_add_module();
        let first = canonical(&m);
        let reparsed = parse_module(&first).expect("parse canonical form");
        let second = canonical(&reparsed);
        assert_eq!(
            first, second,
            "canonical(parse(canonical(m))) must equal canonical(m)"
        );
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical TrustIr text pretty-printer for diff stability (issue #62).
//!
//! [`canonical`] returns the canonical text form of a [`Module`]: the
//! deterministic, idempotent, diff-stable rendering that the `trust-ir-fmt`
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
//! both the canonical module and its string form. Producers that already own
//! a just-built module can use [`into_canonical`] to perform the same rewrite
//! without cloning the complete module first.

use crate::canonicalize::{
    FunctionCanonicalPlan, canonicalize_function, canonicalize_function_with, obligation_owner,
    unique_function_positions,
};
use crate::{Function, Module};

pub use crate::text_loss::{
    FloatSite, NameKind, TextLoss, TextLossError, TextLossKind, is_bare_ident, text_losses,
};

/// Render `module` in canonical TrustIr text form.
///
/// This is the human dump of the canonicalized module. See the module-level
/// documentation for the full definition of "canonical".
///
/// When [`text_losses`] of the canonicalized module is non-empty, the output
/// carries a `; #lossy: <summaries>` line right after the header and the
/// parser REFUSES it (roadmap WS4.2): the text is still printed, for humans,
/// but it can no longer be parsed back into a module that silently lacks the
/// fields. Writers of text meant to be READ BACK (the `trust-ir convert --to
/// text` and `trust-ir-fmt` CLIs, producers' `.trust-ir.txt`) should use
/// [`canonical_checked`], which refuses instead.
///
/// Guaranteed to be idempotent: `canonical(parse(canonical(m))) ==
/// canonical(m)` for every well-formed `m` with `text_losses(m).is_empty()`,
/// when the `parser` feature is enabled.
pub fn canonical(module: &Module) -> String {
    let canon = canonicalize(module);
    format!("{canon}")
}

/// Render `module` in canonical text form, or refuse with every field the
/// text grammar cannot carry (roadmap WS4.2, finding F-065).
///
/// `Ok(text)` is exactly [`canonical`]`(module)` and carries no `#lossy`
/// marker; for it, `parse_module(text)` rebuilds [`canonicalize`]`(module)`
/// field for field. `Err` lists every [`TextLoss`] of the canonicalized
/// module — use the binary, JSON or MessagePack codec instead.
///
/// # Errors
///
/// [`TextLossError`] when [`text_losses`] of the canonicalized module is
/// non-empty.
pub fn canonical_checked(module: &Module) -> Result<String, TextLossError> {
    let canon = canonicalize(module);
    let losses = text_losses(&canon);
    if losses.is_empty() {
        Ok(format!("{canon}"))
    } else {
        Err(TextLossError { losses })
    }
}

/// Render `module` in text form EXACTLY as it is stored — no canonical
/// rewrite — or refuse with every field the text grammar cannot carry.
///
/// This is the transport spelling of the text format, as distinct from
/// [`canonical_checked`]'s diff-stable one. It prints the module's OWN SSA
/// value ids, its own block order and its own parameter-attribute table, so
/// for any module (canonical or not) with no [`text_losses`]:
///
/// ```text
/// parse_module(&text_checked(m).unwrap()) == Ok(m)
/// ```
///
/// and therefore `bin -> text -> bin` is byte-identical. [`canonical_checked`]
/// guarantees that identity only for a module already in canonical form
/// (`m == canonicalize(m)`): on any other module it renumbers SSA values
/// densely and reorders blocks FIRST, so what parses back is
/// [`canonicalize`]`(m)`, not `m` — a silent rewrite that `text_losses`
/// deliberately does not report, because canonicalization is a declared
/// transform rather than a grammar gap. Writers whose text is meant to be read
/// back into the same module (the `trust-ir convert --to text` transport, a
/// producer's `.trust-ir.txt` sidecar) want this function; writers that want a
/// stable diff across producers (the `trust-ir-fmt` binary) want
/// [`canonical_checked`].
///
/// Sparse and out-of-order value ids are legal in a module — SSA validation
/// requires unique definitions and dominance, not density, and the binary
/// codec writes each id verbatim — so preserving them here loses nothing the
/// other codecs keep.
///
/// # Errors
///
/// [`TextLossError`] when [`text_losses`]`(module)` is non-empty.
pub fn text_checked(module: &Module) -> Result<String, TextLossError> {
    let losses = text_losses(module);
    if losses.is_empty() {
        Ok(format!("{module}"))
    } else {
        Err(TextLossError { losses })
    }
}

/// Return a new [`Module`] whose SSA values have been renumbered to a
/// dense canonical 0..N per function.
///
/// The returned in-memory module preserves every field unless canonicalization
/// actually rewrites that function. A rewritten function loses
/// [`Function::source_provenance`]: an ordinary syntactic transform is not
/// authorized to re-seal compiler source authority for a changed artifact.
/// Its canonical text can be fed back through the parser when `parser` is
/// enabled and [`text_losses`] is empty; a module with fields the text
/// grammar cannot carry prints with a refused `; #lossy:` marker — use binary
/// or serde when those facts must survive. WS4.5 carries the layout and
/// linkage surface: struct field names and offsets, enum LAYOUT DESCRIPTORS
/// (a descriptor that contradicts its own enum is still refused — see
/// [`TextLoss::EnumLayout`]), enum variant field names (`Name(field: ty, ..)`;
/// a list not parallel to the fields is refused —
/// [`TextLoss::EnumFieldNames`]), the `switch` exhaustiveness hint
/// (`.. ] exhaustive`) and `global_asm` blocks (`global_asm "<escaped>"`).
/// The proof surface — function summaries, clause bindings, certificate
/// assurance, `clean_cic` kernel re-check directives, the v41 obligation kinds
/// and the v46 typed spec carrier — is carried as of WS4.4.
///
/// Callers that want only the text form should use [`canonical`]
/// directly.
pub fn canonicalize(module: &Module) -> Module {
    into_canonical(module.clone())
}

/// Consume and canonicalize an owned [`Module`] without first cloning it.
///
/// This performs exactly the same deterministic block ordering, dense SSA
/// renumbering, parameter-attribute trimming, and source-provenance handling
/// as [`canonicalize`]. It is intended for producer pipelines that can
/// canonicalize once immediately after construction, before binding proof or
/// cache authority, so later canonical binary identities can take their
/// no-remap function-body path instead of rebuilding fallback value maps.
///
/// The operation is syntactic preparation, not validation or proof. A
/// function whose stored representation changes loses its
/// [`Function::source_provenance`] exactly as it does under [`canonicalize`].
/// The inherited legacy comparison also drops provenance from an otherwise
/// canonical function containing a non-reflexive `f64::NAN` in a bounded-output
/// proof or dialect attribute (but not in a float constant).
///
/// Existing obligations, certificates, proof annotations, and external cache
/// entries are neither cleared nor re-sealed by this helper. Callers must run
/// normal validation and bind any source/proof/cache authority to the returned
/// module rather than treating retained metadata as automatically rebound.
/// Because exact module serialization retains stored SSA and block order, this
/// rewrite can change [`Module::stable_digest`].
/// [`Module::executable_content_digest_v1`] remains invariant only when source
/// provenance is absent or preserved; invalidating provenance changes that
/// deliberately provenance-bearing identity as well.
///
/// # Clause bindings (roadmap WS4.4, NEW-1)
///
/// A `ClausePlace::Value(v)` binding names an SSA value of its owning
/// function, so it is renumbered WITH that function: the function's own
/// summary clauses, and the bindings of every module obligation whose
/// `function` scope (else its `site`'s function) is the rewritten function.
/// Before WS4.4 the body was renumbered and the bindings were not, so a
/// binding silently re-pointed at whichever value took its old number. A
/// binding naming a value the function does not define is kept OUTSIDE the
/// renumbered range (never rebound), so the validator still refuses it. The
/// bindings sit inside the obligation's lineage and content digests, so a
/// certificate bound before the rewrite no longer matches after it: that is
/// the fail-closed outcome, and the reason to bind authority to the RETURNED
/// module. A module with no `Value` binding is rewritten exactly as before.
#[must_use]
pub fn into_canonical(mut module: Module) -> Module {
    let plans: Vec<FunctionCanonicalPlan> = module
        .functions
        .iter()
        .map(FunctionCanonicalPlan::new)
        .collect();
    let positions = unique_function_positions(&module);
    for obligation in &mut module.proof_obligations {
        let Some(&position) = obligation_owner(obligation).and_then(|id| positions.get(&id)) else {
            continue;
        };
        if let Some(formula) = obligation.formula.as_mut() {
            plans[position].remap_formula_bindings(formula);
        }
    }
    for (function, plan) in module.functions.iter_mut().zip(&plans) {
        canonicalize_function_with(function, plan);
    }
    module
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
///
/// The function's `summary` is deliberately NOT part of this rendering, even
/// though WS4.4 made `Display` print it (`; #summary:` block): the obligation
/// digest encodes the summary's clauses itself, and EXCLUDES its `proved` bit
/// and `backed_by` citation (verification progress is bookkeeping, not
/// identity — a cache keyed on it would self-invalidate on discharge). Printing
/// the summary here would fold `proved` back in through the text, so it is
/// stripped first and the pre-WS4.4 rendering — and every obligation digest —
/// is unchanged.
pub(crate) fn canonical_function(func: &Function) -> String {
    let mut canon = func.clone();
    canon.summary = None;
    canonicalize_function(&mut canon);
    format!("{canon}")
}

/// Canonicalize a function in place: sort blocks by `block.id`, then
/// rewrite every `ValueId` that appears in the function (definitions and
/// uses) via the dense remap table.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::Block;
    use crate::SourceProvenance;
    use crate::canonicalize::FunctionCanonicalPlan;
    use crate::inst::{BinOp, ICmpOp, Inst};
    use crate::node::InstrNode;
    use crate::proof::{ProofAnnotation, ProofDigest};
    use crate::ty::{FuncTy, Ty};
    use crate::value::{BlockId, FuncId, ValueId};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    fn source_carrier() -> SourceProvenance {
        SourceProvenance::new(
            ProofDigest::sha256([1; 32]),
            ProofDigest::sha256([2; 32]),
            Vec::new(),
        )
    }

    /// `fn add(i64 %0, i64 %1) -> i64 { %2 = add %0, %1; ret %2 }`
    /// But with sparse SSA numbering: %17, %19, %23.
    fn sparse_add_module() -> Module {
        let mut module = Module::new("sparse_add");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    /// v61 (roadmap WS1.12(c)): a license's `GateEvidence` survives
    /// canonicalization, because the body digest it names is taken over the
    /// canonical image (`executable_content_digest_v1` projects every
    /// function through the same plan). Canonicalizing is not a rewrite the
    /// evidence has to be dropped for — and a real rewrite still moves the
    /// digest.
    #[test]
    fn canonicalize_keeps_gate_evidence_valid() {
        let mut sparse = sparse_add_module();
        let fid = sparse.functions[0].id;
        let digest = sparse.function_body_digest(fid).expect("digest");
        sparse.functions[0].body_gate = Some(crate::BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(crate::GateEvidence {
                obligation: crate::ProofId::new(0),
                body_digest: digest,
            }),
        });
        let dense = canonicalize(&sparse);
        assert_ne!(
            dense.functions[0].blocks, sparse.functions[0].blocks,
            "control: canonicalization renumbered the body"
        );
        assert_eq!(dense.function_body_digest(fid), Ok(digest));
        assert_eq!(dense.functions[0].body_gate, sparse.functions[0].body_gate);

        let mut rewritten = dense;
        rewritten.functions[0].blocks[0].body[0].inst = Inst::BinOp {
            op: BinOp::Sub,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        };
        assert_ne!(rewritten.function_body_digest(fid), Ok(digest));
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
    fn owned_canonicalization_matches_borrowed_without_cloning_the_module_owner() {
        let module = sparse_add_module();
        let expected = canonicalize(&module);
        let expected_executable_digest = module.executable_content_digest_v1();
        let original_stable_digest = module.stable_digest();
        let module_name_allocation = module.name.as_ptr();

        let actual = into_canonical(module);

        assert_eq!(actual, expected);
        assert_eq!(
            actual.executable_content_digest_v1(),
            expected_executable_digest
        );
        assert_ne!(actual.stable_digest(), original_stable_digest);
        assert_eq!(
            actual.name.as_ptr(),
            module_name_allocation,
            "the consuming path must retain the owned module-name allocation"
        );
        assert!(
            actual
                .functions
                .iter()
                .all(|function| FunctionCanonicalPlan::new_if_needed(function).is_none()),
            "the owned result must not require a fallback function remap plan"
        );
    }

    #[test]
    fn owned_canonicalization_does_not_preserve_a_digest_after_provenance_invalidation() {
        let mut module = sparse_add_module();
        module.functions[0].source_provenance = Some(source_carrier());
        let original_executable_digest = module.executable_content_digest_v1();

        let actual = into_canonical(module);

        assert!(actual.functions[0].source_provenance.is_none());
        assert_ne!(
            actual.executable_content_digest_v1(),
            original_executable_digest,
            "executable-content identity retains source provenance"
        );
    }

    #[test]
    fn owned_canonicalization_preserves_legacy_nan_provenance_behavior() {
        let mut plain = into_canonical(sparse_add_module());
        plain.functions[0].source_provenance = Some(source_carrier());

        let mut constant_nan = plain.clone();
        constant_nan.functions[0].blocks[0].body.insert(
            1,
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: crate::Constant::Float(f64::NAN),
            })
            .with_result(v(3)),
        );
        assert!(
            into_canonical(constant_nan).functions[0]
                .source_provenance
                .is_some(),
            "float constants compare by their bit pattern"
        );

        let mut bounded_nan = plain.clone();
        bounded_nan.functions[0]
            .proofs
            .push(ProofAnnotation::BoundedOutput {
                lo: f64::NAN,
                hi: 1.0,
            });
        assert!(
            into_canonical(bounded_nan).functions[0]
                .source_provenance
                .is_none(),
            "legacy derived PartialEq invalidates provenance for bounded NaN"
        );

        let mut dialect_nan = plain;
        dialect_nan.functions[0].blocks[0].body.insert(
            1,
            InstrNode::new(Inst::DialectOp(Box::new(
                crate::dialect::DialectInst::new("fixture", "nan")
                    .with_operand(v(0))
                    .with_result_ty(Ty::I64)
                    .with_attr("nan", crate::dialect::AttrValue::F64(f64::NAN)),
            )))
            .with_result(v(3)),
        );
        assert!(
            into_canonical(dialect_nan).functions[0]
                .source_provenance
                .is_none(),
            "legacy derived PartialEq invalidates provenance for dialect NaN"
        );
    }

    #[test]
    fn canonicalize_invalidates_only_when_it_rewrites_source_bound_body() {
        let mut sparse = sparse_add_module();
        sparse.functions[0].source_provenance = Some(source_carrier());
        let dense = canonicalize(&sparse);
        assert!(
            dense.functions[0].source_provenance.is_none(),
            "SSA renumbering must invalidate compiler source authority"
        );

        let mut already_dense = dense;
        already_dense.functions[0].source_provenance = Some(source_carrier());
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
        let ft = m
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        m.try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let ft = dense
            .add_func_type(FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        dense
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let sparse = sparse_add_module();
        assert_eq!(canonical(&sparse), canonical(&dense));
    }

    #[test]
    fn canonical_sorts_blocks_by_id() {
        let mut module = Module::new("blocks");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let c = canonicalize(&module);
        let ids: Vec<u32> = c.functions[0].blocks.iter().map(|b| b.id.index()).collect();
        assert_eq!(ids, vec![0, 1, 2], "blocks must be sorted by id");
    }

    #[test]
    fn canonical_preserves_proof_annotations() {
        let mut module = Module::new("proofs");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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

    // ------------------------------------------------------------------
    // Roadmap WS4.4, NEW-1: `ClausePlace::Value` bindings follow the SSA
    // renumbering of their owning function.
    // ------------------------------------------------------------------

    fn value_bound(value: ValueId) -> crate::proof::ProofFormula {
        let mut formula = crate::proof::ProofFormula::smtlib2("(= r 1)", "Bool");
        formula.bindings = vec![(
            "r".to_string(),
            crate::proof::ClauseBinding {
                sort: crate::proof::ClauseSort::BitVec(64),
                place: crate::proof::ClausePlace::Value(value),
            },
        )];
        formula
    }

    fn bound_value(formula: &crate::proof::ProofFormula) -> ValueId {
        match formula.bindings[0].1.place {
            crate::proof::ClausePlace::Value(value) => value,
            other => panic!("expected a Value binding, got {other:?}"),
        }
    }

    /// `sparse_add_module` (`%17, %19 -> %23`, renumbered to `%0, %1 -> %2`)
    /// with an `ensures` bound to `%23`, a module obligation SCOPED to the
    /// function bound to `%23`, and one scoped only by its `site`.
    fn sparse_add_with_value_bindings() -> Module {
        use crate::proof::{ObligationKind, ObligationSite, ProofObligation, ProofStatus};
        use crate::value::ProofId;
        let mut module = sparse_add_module();
        module.functions[0].summary = Some(
            crate::FunctionSummary::new()
                .with_params(vec!["a".into(), "b".into()])
                .ensuring(value_bound(v(23))),
        );
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Postcondition,
                ProofStatus::Pending,
                "scoped",
            )
            .with_function(FuncId::new(0))
            .with_formula(value_bound(v(23))),
        );
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::MemorySafety,
                ProofStatus::Pending,
                "sited",
            )
            .with_site(ObligationSite::new(FuncId::new(0), b(0), 0))
            .with_formula(value_bound(v(19))),
        );
        module
    }

    /// The roadmap's NEW-1 test: before WS4.4 the body was renumbered and the
    /// bindings were not, so `%23` stayed `%23` — a value the canonical
    /// function no longer defines — or, worse, named whichever value took the
    /// old number. Now each binding names the SAME value it named before.
    #[test]
    fn new1_value_bindings_follow_the_canonical_renumbering() {
        let module = sparse_add_with_value_bindings();
        let canon = canonicalize(&module);
        assert_eq!(canon.functions[0].blocks[0].body[0].results[0], v(2));
        let summary = canon.functions[0].summary.as_ref().unwrap();
        assert_eq!(bound_value(&summary.ensures[0]), v(2), "summary ensures");
        assert_eq!(
            bound_value(canon.proof_obligations[0].formula.as_ref().unwrap()),
            v(2),
            "a `function`-scoped obligation"
        );
        assert_eq!(
            bound_value(canon.proof_obligations[1].formula.as_ref().unwrap()),
            v(1),
            "a `site`-scoped obligation (`%19` is the second parameter)"
        );
        // The owned path agrees, and the rewrite is idempotent.
        assert_eq!(into_canonical(module.clone()), canon);
        assert_eq!(canonicalize(&canon), canon);
    }

    /// A binding naming a value the function does NOT define stays dangling:
    /// it is moved OUT of the renumbered range rather than left at a number
    /// the rewrite reassigns (`%1` would otherwise silently name the second
    /// parameter after canonicalization).
    #[test]
    fn new1_a_dangling_value_binding_is_never_rebound() {
        let mut module = sparse_add_module();
        module.functions[0].summary = Some(
            crate::FunctionSummary::new()
                .with_params(vec!["a".into(), "b".into()])
                .ensuring(value_bound(v(1)))
                .ensuring(value_bound(v(40))),
        );
        let canon = canonicalize(&module);
        let summary = canon.functions[0].summary.as_ref().unwrap();
        // Three definitions (`%0..%2` after the rewrite): `%1` is moved to
        // 3 + 1, and `%40` (already outside the range) is kept.
        assert_eq!(bound_value(&summary.ensures[0]), v(4));
        assert_eq!(bound_value(&summary.ensures[1]), v(40));
        assert_eq!(canonicalize(&canon), canon, "idempotent");
    }

    /// An obligation whose scope names no function, or a duplicated id, is
    /// not remapped against a guess (the validator refuses its scope).
    #[test]
    fn new1_unresolvable_owner_is_not_remapped() {
        let mut module = sparse_add_with_value_bindings();
        module.proof_obligations[0].function = Some(FuncId::new(9));
        let mut duplicate = module.functions[0].clone();
        duplicate.name = "twin".into();
        module.functions.push(duplicate);
        module.proof_obligations[1].site =
            Some(crate::proof::ObligationSite::new(FuncId::new(0), b(0), 0));
        let canon = canonicalize(&module);
        assert_eq!(
            bound_value(canon.proof_obligations[0].formula.as_ref().unwrap()),
            v(23)
        );
        assert_eq!(
            bound_value(canon.proof_obligations[1].formula.as_ref().unwrap()),
            v(19),
            "FuncId 0 names two functions"
        );
    }

    /// A module WITHOUT `Value` bindings is rewritten exactly as before:
    /// identity-neutral for the whole existing corpus.
    #[test]
    fn new1_is_identity_neutral_without_value_bindings() {
        let mut module = sparse_add_module();
        let mut world = value_bound(v(23));
        world.bindings[0].1.place = crate::proof::ClausePlace::Param { index: 0 };
        module.functions[0].summary = Some(crate::FunctionSummary::new().ensuring(world.clone()));
        let canon = canonicalize(&module);
        assert_eq!(
            canon.functions[0].summary.as_ref().unwrap().ensures[0],
            world
        );
    }

    /// The obligation digest's function-content text does NOT include the
    /// summary block `Display` prints since WS4.4: the digest excludes the
    /// summary's `proved` bit (verification progress is not identity), so
    /// flipping it must not move the digest.
    #[test]
    fn obligation_digest_ignores_the_printed_summary_block() {
        use crate::value::ProofId;
        let module = sparse_add_with_value_bindings();
        let before = module.obligation_digest(ProofId::new(0)).unwrap();
        let mut proved = module.clone();
        proved.functions[0].summary.as_mut().unwrap().proved = true;
        proved.functions[0].summary.as_mut().unwrap().backed_by =
            Some(crate::ExternRef::new(crate::value::ImportId::new(0), "x"));
        assert_eq!(proved.obligation_digest(ProofId::new(0)).unwrap(), before);
        assert!(!canonical_function(&proved.functions[0]).contains("#summary"));
    }
}

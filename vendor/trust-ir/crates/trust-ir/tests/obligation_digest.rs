// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// v23 (Program CK1 contract ladder, WS4-M2): `Module::obligation_digest` —
// the SHA-256 content-address of a (module, obligation) pair used as the
// cert-cache key. The properties pinned here ARE the cache-correctness
// contract:
//
// 1. **Stability** (known-answer): the digest of a fixed module/obligation is
//    a pinned constant. If this test fails, every persisted cert cache in the
//    ecosystem silently invalidates — bump the digest domain string instead of
//    quietly changing the byte layout.
// 2. **Body edit invalidates exactly its digest** (WS4-M2): editing the
//    scoped function's body changes that obligation's digest; obligations
//    scoped elsewhere (or module-scoped) keep theirs.
// 3. **Renumbering insensitivity**: SSA value renumbering, block-vector
//    reordering, and function declaration order — the changes
//    `trust-ir-diff` ignores — leave the digest unchanged (the eventual
//    WS4-M2 contract is digest-equal ⟺ diff-clean).
// 4. **Status is not identity**: flipping `ProofStatus` (the mutable
//    verification-progress label) never shifts the digest, or the cache
//    would self-invalidate on discharge.
// 5. **Contract and entry are identity** (introduced in digest domain v2 and
//    preserved by v3/v4 framing): the owning function's `summary`
//    (`requires`/`ensures`/`params`) and `entry` block are hashed even though
//    the canonical text carries neither — a cached certificate may have
//    assumed the contract, and entry decides execution order, so editing either
//    MUST invalidate the slot. The summary's `proved` flag is excluded
//    (verification progress, like `ProofStatus`).

#![cfg(feature = "fmt")]

use trust_ir::inst::{BinOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    ObligationKind, ProofFormula, ProofObligation, ProofObligationSourceIdentity,
    ProofObligationSourceRange, ProofStatus, PublicObligationIdentity,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, ProofId, ValueId};
use trust_ir::{Block, Function, Module, ProofDigest};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// `@target`: two blocks — `bb0(%a, %b): %c = add %a, %b; br bb1(%c)` and
/// `bb1(%d): ret %d` — built with a caller-chosen SSA numbering base and
/// block-vector push order (block IDs are fixed; only the Vec order varies).
fn target_function(
    ft: trust_ir::value::FuncTyId,
    value_base: u32,
    blocks_reversed: bool,
) -> Function {
    let a = v(value_base);
    let bv = v(value_base + 7);
    let c = v(value_base + 13);
    let d = v(value_base + 21);

    let mut entry = Block::new(b(0));
    entry.params.push((a, Ty::I64));
    entry.params.push((bv, Ty::I64));
    entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: a,
            rhs: bv,
        })
        .with_result(c),
    );
    entry.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![c],
    }));

    let mut exit = Block::new(b(1));
    exit.params.push((d, Ty::I64));
    exit.body
        .push(InstrNode::new(Inst::Return { values: vec![d] }));

    let mut func = Function::new(FuncId::new(0), "target", ft, b(0));
    if blocks_reversed {
        func.blocks = vec![exit, entry];
    } else {
        func.blocks = vec![entry, exit];
    }
    func
}

/// `@other`: `bb0: ret` — the neighbor function edits must NOT leak into
/// `@target`-scoped digests.
fn other_function(ft: trust_ir::value::FuncTyId) -> Function {
    let mut block = Block::new(b(0));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut func = Function::new(FuncId::new(1), "other", ft, b(0));
    func.blocks.push(block);
    func
}

/// The fixed module behind the known-answer pin: `@target` + `@other`, one
/// obligation scoped to each, one module-scoped obligation.
fn base_module(value_base: u32, blocks_reversed: bool, functions_swapped: bool) -> Module {
    let mut m = Module::new("obligation_digest");
    let ft_bin = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let ft_unit = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let target = target_function(ft_bin, value_base, blocks_reversed);
    let other = other_function(ft_unit);
    if functions_swapped {
        m.add_function(other);
        m.add_function(target);
    } else {
        m.add_function(target);
        m.add_function(other);
    }

    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "result is the sum of the operands",
        )
        .with_function(FuncId::new(0))
        .with_formula(ProofFormula::smtlib2("(= result (bvadd a b))", "Bool")),
    );
    m.proof_obligations.push(ProofObligation::new(
        ProofId::new(1),
        ObligationKind::TypeInvariant,
        ProofStatus::Pending,
        "module-scoped invariant",
    ));
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(2),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "other never panics",
        )
        .with_function(FuncId::new(1)),
    );
    m
}

fn digest_hex(m: &Module, id: u32) -> String {
    m.obligation_digest(ProofId::new(id))
        .unwrap_or_else(|| panic!("obligation {id} must have a digest"))
        .to_string()
}

/// (1) Known-answer stability: the pinned SHA-256 of the fixed
/// (module, obligation) pairs. A change here is a cache-invalidation event
/// for every consumer — never rewrite the pin casually; bump the digest
/// domain (`trust_ir.obligation.digest.v4`) on a deliberate layout change.
/// (v1 → v2: `entry` + `summary` joined the layout — the soundness fix for
/// contract-weakening cache replays. v2 → v3: canonical domain framing and
/// checked 64-bit lengths replaced the ad hoc preimage encoding. v3 → v4:
/// embedded source/public proof-unit identity joined the claim.)
#[test]
fn obligation_digest_sha256_known_answer() {
    let m = base_module(0, false, false);
    assert_eq!(
        digest_hex(&m, 0),
        "sha256:88ca7654f11c4084a1cea1c396c1b29aec5782390d89e2915d7b11c80b5d0a4b",
        "function-scoped obligation digest drifted"
    );
    assert_eq!(
        digest_hex(&m, 1),
        "sha256:9e7a8a41f7d816edfbdaaf0bc657936156f1997d8a291b0c72093867954902dd",
        "module-scoped obligation digest drifted"
    );
}

/// The digest resolves only real content: an unknown obligation id and a
/// dangling function scope both yield `None` (nothing addressable to cache).
#[test]
fn obligation_digest_is_none_for_unknown_or_dangling() {
    let mut m = base_module(0, false, false);
    assert!(m.obligation_digest(ProofId::new(99)).is_none());
    m.proof_obligations[0].function = Some(FuncId::new(42));
    assert!(
        m.obligation_digest(ProofId::new(0)).is_none(),
        "a dangling function scope has no addressable content"
    );
}

#[test]
fn obligation_digest_binds_every_embedded_source_identity_field() {
    let mut module = base_module(0, false, false);
    module.proof_obligations[0].source = Some(
        ProofObligationSourceIdentity::new("rust:crate::target", "assertion α")
            .with_range(ProofObligationSourceRange {
                file: 2,
                start_line: 11,
                start_col: 3,
                end_line: 12,
                end_col: 9,
            })
            .with_public(PublicObligationIdentity {
                obligation_id: "vc:crate::target:0".to_string(),
                semantic_digest: ProofDigest::sha256([7; 32]),
            }),
    );
    let digest = module.obligation_digest(ProofId::new(0)).unwrap();
    let mutations: &[fn(&mut ProofObligationSourceIdentity)] = &[
        |source| source.source_id.push('!'),
        |source| source.assertion_id.push('!'),
        |source| source.range.as_mut().unwrap().file += 1,
        |source| source.range.as_mut().unwrap().start_line += 1,
        |source| source.range.as_mut().unwrap().start_col += 1,
        |source| source.range.as_mut().unwrap().end_line += 1,
        |source| source.range.as_mut().unwrap().end_col += 1,
        |source| source.public.as_mut().unwrap().obligation_id.push('!'),
        |source| source.public.as_mut().unwrap().semantic_digest.bytes[0] ^= 1,
    ];
    for mutate in mutations {
        let mut changed = module.clone();
        mutate(changed.proof_obligations[0].source.as_mut().unwrap());
        assert_ne!(changed.obligation_digest(ProofId::new(0)).unwrap(), digest);
    }
}

/// (2) WS4-M2 falsifier: a body edit invalidates exactly its digest — the
/// edited function's obligation changes; the other-function-scoped and
/// module-scoped obligations keep theirs.
#[test]
fn body_edit_invalidates_exactly_its_digest() {
    let before = base_module(0, false, false);
    let mut after = base_module(0, false, false);
    // Edit @target's body: add -> mul.
    let target = after
        .functions
        .iter_mut()
        .find(|f| f.name == "target")
        .unwrap();
    if let Inst::BinOp { op, .. } = &mut target.blocks[0].body[0].inst {
        *op = BinOp::Mul;
    } else {
        panic!("expected the add node");
    }

    assert_ne!(
        digest_hex(&before, 0),
        digest_hex(&after, 0),
        "editing the scoped function's body MUST invalidate the digest"
    );
    assert_eq!(
        digest_hex(&before, 1),
        digest_hex(&after, 1),
        "module-scoped obligation is not affected by a function body edit"
    );
    assert_eq!(
        digest_hex(&before, 2),
        digest_hex(&after, 2),
        "an obligation scoped to a DIFFERENT function keeps its digest"
    );
}

/// (2b) Editing a different function leaves the digest unchanged.
#[test]
fn editing_a_different_function_leaves_digest_unchanged() {
    let before = base_module(0, false, false);
    let mut after = base_module(0, false, false);
    // Edit @other's body: give its return a preceding const via a new node.
    let other = after
        .functions
        .iter_mut()
        .find(|f| f.name == "other")
        .unwrap();
    other.blocks[0]
        .body
        .insert(0, InstrNode::new(Inst::Unreachable));

    assert_eq!(
        digest_hex(&before, 0),
        digest_hex(&after, 0),
        "@target-scoped digest must not move when @other is edited"
    );
    assert_ne!(
        digest_hex(&before, 2),
        digest_hex(&after, 2),
        "@other-scoped digest must move when @other is edited"
    );
}

/// (3) Renumbering insensitivity: sparse SSA renumbering, block-vector
/// reordering (same block ids), and function declaration order are exactly
/// the perturbations `trust-ir-diff` ignores — the digest ignores them too.
#[test]
fn renumbering_and_reordering_leave_digest_unchanged() {
    let canonical = base_module(0, false, false);
    let renumbered = base_module(1000, false, false);
    let blocks_reversed = base_module(0, true, false);
    let functions_swapped = base_module(0, false, true);

    let pin = digest_hex(&canonical, 0);
    assert_eq!(
        digest_hex(&renumbered, 0),
        pin,
        "sparse SSA value renumbering must not shift the digest"
    );
    assert_eq!(
        digest_hex(&blocks_reversed, 0),
        pin,
        "block Vec order (same block ids) must not shift the digest"
    );
    assert_eq!(
        digest_hex(&functions_swapped, 0),
        pin,
        "function declaration order must not shift the digest"
    );
}

/// (4) Status is not identity: discharging (or failing) an obligation leaves
/// its digest fixed, so a cert cache keyed on the digest survives the
/// verification lifecycle.
#[test]
fn obligation_status_flip_leaves_digest_unchanged() {
    let pending = base_module(0, false, false);
    let pin = digest_hex(&pending, 0);
    for status in [
        ProofStatus::Discharged,
        ProofStatus::Failed,
        ProofStatus::Trusted,
        ProofStatus::Certified,
    ] {
        let mut flipped = base_module(0, false, false);
        flipped.proof_obligations[0].status = status;
        assert_eq!(
            digest_hex(&flipped, 0),
            pin,
            "ProofStatus::{status:?} is bookkeeping, not identity"
        );
    }
}

/// The claim is identity: a changed formula (same function content) moves
/// the digest — two different obligations about the same body must not
/// collide onto one cache slot.
#[test]
fn formula_change_invalidates_digest() {
    let before = base_module(0, false, false);
    let mut after = base_module(0, false, false);
    after.proof_obligations[0].formula =
        Some(ProofFormula::smtlib2("(= result (bvmul a b))", "Bool"));
    assert_ne!(digest_hex(&before, 0), digest_hex(&after, 0));
}

/// (5) The contract is identity: weakening (here: dropping) a `requires`
/// clause of the scoped function's summary MUST move the digest. A cached
/// certificate proved under the stronger precondition would otherwise be
/// replayed for the weakened contract — the unsound cache-hit direction.
/// Contract-only declarations (body-less summaries) make this the ONLY
/// meaningful content, so it cannot live outside the key.
#[test]
fn summary_change_invalidates_digest() {
    use trust_ir::FunctionSummary;

    let with_contract = |requires: Vec<ProofFormula>| {
        let mut m = base_module(0, false, false);
        let target = m.functions.iter_mut().find(|f| f.name == "target").unwrap();
        target.summary = Some(
            FunctionSummary::new()
                .with_params(vec!["a".into(), "b".into()])
                .ensuring(ProofFormula::smtlib2("(= result (bvadd a b))", "Bool")),
        );
        for clause in requires {
            let s = target.summary.take().unwrap();
            target.summary = Some(s.requiring(clause));
        }
        m
    };

    let strong = with_contract(vec![ProofFormula::smtlib2("(bvsgt a #x00)", "Bool")]);
    let weakened = with_contract(vec![]);
    let none = base_module(0, false, false);

    assert_ne!(
        digest_hex(&strong, 0),
        digest_hex(&weakened, 0),
        "dropping a requires clause MUST invalidate the digest"
    );
    assert_ne!(
        digest_hex(&weakened, 0),
        digest_hex(&none, 0),
        "attaching a summary at all MUST invalidate the digest"
    );
    assert_eq!(
        digest_hex(&strong, 1),
        digest_hex(&none, 1),
        "module-scoped obligation is not affected by a summary edit"
    );
}

/// (5b) `summary.proved` is bookkeeping, not identity: like `ProofStatus`,
/// it flips when verification completes, and a cache keyed on it would
/// self-invalidate on discharge.
#[test]
fn summary_proved_flip_leaves_digest_unchanged() {
    use trust_ir::FunctionSummary;

    let with_proved = |proved: bool| {
        let mut m = base_module(0, false, false);
        let target = m.functions.iter_mut().find(|f| f.name == "target").unwrap();
        let mut summary = FunctionSummary::new()
            .with_params(vec!["a".into(), "b".into()])
            .ensuring(ProofFormula::smtlib2("(= result (bvadd a b))", "Bool"));
        summary.proved = proved;
        target.summary = Some(summary);
        m
    };

    assert_eq!(
        digest_hex(&with_proved(false), 0),
        digest_hex(&with_proved(true), 0),
        "proved is verification progress, not contract identity"
    );
}

/// (5c) `entry` is identity: two validator-valid functions with identical
/// block sets but different entry blocks execute differently, yet print to
/// byte-identical canonical text (the text format has no entry marker).
/// The digest hashes `entry` explicitly so they cannot share a cache slot.
#[test]
fn entry_change_invalidates_digest() {
    let before = base_module(0, false, false);
    let mut after = base_module(0, false, false);
    let target = after
        .functions
        .iter_mut()
        .find(|f| f.name == "target")
        .unwrap();
    target.entry = b(1);

    assert_ne!(
        digest_hex(&before, 0),
        digest_hex(&after, 0),
        "an entry-block change MUST invalidate the digest"
    );
    assert_eq!(
        digest_hex(&before, 2),
        digest_hex(&after, 2),
        "an obligation scoped to a DIFFERENT function keeps its digest"
    );
}

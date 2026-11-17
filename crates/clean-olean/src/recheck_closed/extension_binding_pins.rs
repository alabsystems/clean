// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The reviewed worlds the pinned extension-binding table is the union of.
//!
//! A WORLD is one construction of a key's dependency-closed cone that was
//! reviewed as meaning what the kernel's by-name hook for that key computes:
//! a Lean toolchain's own `Init` decoded over an empty base (`lean-<version>`),
//! or that `Init` decoded over the base a consumer snapshots before it imports
//! anything (`clean-import+lean-<version>`: `clean check
//! --imports-prefer-olean`, `clean lake build`). Every row is minted by
//! `examples/measure_recheck_closed.rs --print-extension-bindings`; the
//! workspace pin's worlds are re-derived row for row by
//! `extension_binding_lean_tests.rs`.
//!
//! A key is bound when its fingerprint equals the row of ANY world. That is
//! sound because a fingerprint is a Merkle hash of the key's whole cone — its
//! own declaration and, recursively, every constant it mentions — so equality
//! with a pinned row means the environment holds exactly the reviewed cone, and
//! each world's row was reviewed on its own. Two worlds' cones for one
//! environment can only coexist when they agree on every shared name, and a
//! mixture changes nothing a row certifies: a row vouches for its key's
//! meaning, never for another key's.
//!
//! Adding a world is a claim, not a measurement: the rows say "this is Lean's
//! definition and it computes what the hook computes". The review for each
//! world is in the report its doc comment names.

/// One reviewed world: its label and `(key, fingerprint)` rows.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PinnedWorld {
    /// The world's name, carried into a refusal's `expected`.
    pub(crate) label: &'static str,
    /// `(key, dependency-closed fingerprint)`, one row per key.
    pub(crate) rows: &'static [(&'static str, &'static str)],
}

/// Every reviewed world, in the order a refusal lists them.
pub(crate) const PINNED_WORLDS: &[PinnedWorld] = &[
    PinnedWorld {
        label: "lean-v4.8.0-core",
        rows: LEAN_V4_8_0,
    },
    PinnedWorld {
        label: "lean-v4.30.0-rc2-core",
        rows: LEAN_V4_30_0_RC2,
    },
    PinnedWorld {
        label: "clean-import+lean-v4.30.0-rc2-core",
        rows: CLEAN_IMPORT_LEAN_V4_30_0_RC2,
    },
    PinnedWorld {
        label: "lean-v4.35.0-literals-div-mod",
        rows: LEAN_V4_35_0_PRIMITIVES,
    },
];

/// A deliberately partial 4.35 world, reviewed against the official release's
/// actual decoded definitions and ordinary production checker. It qualifies
/// only these five keys, not every primitive in that release. The report
/// `reports/lean435-primitive-bindings/2026-11-16/README.md` retains the
/// reference review's skipped deep D/P legs, additional actual large-Nat and
/// literal production legs, official positive/negative source checks, and
/// computational-helper/head mutations. The genuine `Init.Prelude` and full
/// `Init` closures re-derive each row independently, including query order.
#[rustfmt::skip]
const LEAN_V4_35_0_PRIMITIVES: &[(&str, &str)] = &[
    ("Char.ofNat", "22d7b4b211530abc668488704af1475d71a1d9224d52d8def1ea2e7cc9748f04"),
    ("Nat.div", "2e16483f581889a8a688521901d0efa6156f1c4771f5e8da86018787ddad327e"),
    ("Nat.mod", "86c4c86b3f767a1167cdc106758b6922ace75943a1612747893bafe6122189cb"),
    ("String", "2177aa56a0d85210fecc5497043bdf0bea74eb6802211854081a6f52a682eee8"),
    ("String.ofList", "a9e871d50baa15cc0ed7edcfc9feb2eca2eb22825e7c2c74d7a225858dbc6a68"),
];

/// `(name, fingerprint)` for the Lean v4.8.0 core declarations, as produced by
/// `ExtensionBindings::derive_from` over the Lean v4.8.0 `.olean` closure
/// (`examples/measure_recheck_closed.rs --print-extension-bindings`). A key
/// that Lean v4.8.0 does not declare (`String.ofList`) has no row, so a
/// declaration of it is refused.
///
/// Measured 2026-09-24: `--root Init` over the v4.8.0 toolchain library (158
/// modules, 13,560 constants) and `--root TrustIr.Proofs.TransformCorrectness`
/// over the TSL build (187 modules, 16,331 constants) print these 35 rows
/// byte-identically. A family member's row is its family's fingerprint.
///
/// Re-measured 2026-09-25 with the five keys added in round 24 (`Eq`,
/// `optParam`, `autoParam`, `outParam`, `semiOutParam`): the same two runs
/// print these 40 rows byte-identically, and the 35 earlier rows are
/// unchanged. Re-measured 2026-09-28 (`--base default --root Init`, every key
/// a target): the same 40 rows, and `String.ofList` still undeclared.
///
/// Re-minted 2026-11-14 (Q4 residuals, `docs/DECISIONS.md`) for the `MData`
/// erasure of ordinary constants (`fingerprint.rs`, `Annotations`), by the
/// 2026-09-28 run (`--base default --root Init`, every key a target, 158
/// modules). The toolchain's `lib/lean` was gone from this Mac, so the run
/// read the same release's `Init` closure (158 `.olean` files) from Trust's
/// `vendor/lean-core-oleans`, each file checked against that directory's
/// `MANIFEST.toml` digest (`leanprover/lean4:v4.8.0`, commit `df668f00e6c0`).
/// 19 rows moved (`Char.ofNat`, `Int.add`, `Int.mul`, `Int.sub`, `Nat.add`,
/// `Nat.beq`, `Nat.ble`, `Nat.div`, `Nat.gcd`, `Nat.land`, `Nat.lor`,
/// `Nat.mod`, `Nat.mul`, `Nat.pow`, `Nat.pred`, `Nat.shiftLeft`,
/// `Nat.shiftRight`, `Nat.sub`, `Nat.xor`); the other 21 are byte-identical
/// to the rows they replace, which is how the bytes were checked to be this
/// world's.
#[rustfmt::skip]
const LEAN_V4_8_0: &[(&str, &str)] = &[
    ("Bool.false", "be3c3f6396fab9e977cfdb4222a39d021172bff22c7d4ad1733223908305813e"),
    ("Bool.true", "be3c3f6396fab9e977cfdb4222a39d021172bff22c7d4ad1733223908305813e"),
    ("Char", "4d79c9627db7a981e22a17e5cca51733db2c9b98b395ad709edea63d4121e12d"),
    ("Char.ofNat", "e3f29404de78389785b22da3ff22e71e57d1c79b7a857de8a15cd99d79acc538"),
    ("Eq", "137a9846542d714510e3861e0086c1fb7be53bd46d706053d54264ede218069f"),
    ("Int", "c6e7343231f2ae48dfac2a151a7ce6b40086d3027392b4dfa990c166be8a9869"),
    ("Int.add", "6f050eedd8cf7583c46a20621a09b12f7ac386ca9dd51a1e381baa81315615b8"),
    ("Int.mul", "fc31d849a71a1191ff319bdf79dbae6f90253715c1ccac3dbf37184ab6ddc83e"),
    ("Int.negSucc", "c6e7343231f2ae48dfac2a151a7ce6b40086d3027392b4dfa990c166be8a9869"),
    ("Int.ofNat", "c6e7343231f2ae48dfac2a151a7ce6b40086d3027392b4dfa990c166be8a9869"),
    ("Int.rec", "c6e7343231f2ae48dfac2a151a7ce6b40086d3027392b4dfa990c166be8a9869"),
    ("Int.sub", "b9bfd432f5674ed14d230c0ce825a07ea59242575381a1029e48bafbd666e0f0"),
    ("Lean.reduceBool", "5f112414286d8983fa842e241915e914e408d18f919ef12a919c4ead5c6f12de"),
    ("Lean.reduceNat", "31b629c73a4d6f435827eb75e5787692bd6af1bd57df7c20bff81d47a8473f27"),
    ("List.cons", "9d4c05548ea48d9614e5b99f7b29242067d6232eada9d0541af740f40b194b68"),
    ("List.nil", "9d4c05548ea48d9614e5b99f7b29242067d6232eada9d0541af740f40b194b68"),
    ("Nat", "97a4bfe636afd7e2bb7ec71fee26a2142b745a949fb6d29e8009a90eea3a2ca5"),
    ("Nat.add", "7b512f634486ae8e4e4b0418c982c4a6ffd545f583400634af315e574d45b8b1"),
    ("Nat.beq", "c31b947f7540480f2cf67e055b3b1565fb6023de276aff2477df951a57bbcbb5"),
    ("Nat.ble", "fc5481825261518e5ca9b12f409b395e5548295c66b9dc3425861437f29dcfea"),
    ("Nat.div", "19aba529de94d86de6a7cabd46a21a897f9f8041aaed9849c6354cb21c02c3d6"),
    ("Nat.gcd", "1e65921fa90299da8c35ca7b90940432e3b1204551d4cd75d01fbd9502d80223"),
    ("Nat.land", "60b43795fa49b600086bcbd013991a0b432462121e3cdd5d59db97b2cf73dcdd"),
    ("Nat.lor", "67e0aacd569d31c03889c3df6292f38fd7f6cf39d817a06abf3ba3bffb3b4639"),
    ("Nat.mod", "98f6dbe53739cf8848f9488fe272cc7330d81bfce4199138e6c67a3b3753f327"),
    ("Nat.mul", "2b680144f42f1e4111a64866e0aab1f4d7202e6ddee386e74858235ab688f304"),
    ("Nat.pow", "295321dd52d05b26e06bcecb2e4db801691a327ca92fdcf461fef1b1098fd2be"),
    ("Nat.pred", "52a04ff0fbed5ddf88217892e7b2e3605dc3b0e59bf1fd92b0c89b4a28c3f78c"),
    ("Nat.rec", "97a4bfe636afd7e2bb7ec71fee26a2142b745a949fb6d29e8009a90eea3a2ca5"),
    ("Nat.shiftLeft", "a5bcf69c436132d8501fcc34bc782e8aea0944c9ded4859d1fa6dc3229c04964"),
    ("Nat.shiftRight", "a5c40dc83757ce4ade46bce268695b2c574beb649e86fa68c9c64c5be43d8fcf"),
    ("Nat.sub", "4073997f1a1de9fc5da390cba0f2bf093297c0b54eafc756de616e811291973c"),
    ("Nat.succ", "97a4bfe636afd7e2bb7ec71fee26a2142b745a949fb6d29e8009a90eea3a2ca5"),
    ("Nat.xor", "58975c96f55cd289923992b78c4819ff5756e187ef4adbe641f3a7e13f679a2d"),
    ("Nat.zero", "97a4bfe636afd7e2bb7ec71fee26a2142b745a949fb6d29e8009a90eea3a2ca5"),
    ("String", "d3817c27dc6bb26f932749023bce386ac3ba626c43150f0069ce5ac6f11d9667"),
    ("autoParam", "984d19cc1d8447f20a23c33bacf00ae508d46ce1c2f5867338b2de1469421f39"),
    ("optParam", "d36875cfbfeb0985d655497e0541dc038def771f74a4be30bd205f5f18e6a4ab"),
    ("outParam", "75fc9ffa3b4256dbd1b75f8f5ee23e379f17128ff4906c957cc8cde1d6628751"),
    ("semiOutParam", "888d5a2634e22b1b9ea6211e0b794baa559edb234a31a651eff5a9df96cf5a9a"),
];

/// `(name, fingerprint)` for the Lean v4.30.0-rc2 core declarations — the
/// workspace pin, and the toolchain the source-elab corpus is built with —
/// decoded over an EMPTY base (`Environment::for_lean_replay`, what the
/// `.olean` re-check lanes start from; `Environment::default()` prints the
/// same rows). Every one of the 41 keys is declared; `String.ofList` exists
/// here (v4.30's `String` is a `ByteArray` structure and `String.ofList` its
/// list constructor), which is the string-literal expansion the kernel uses.
///
/// Measured 2026-09-28 (`reports/2026-09-28-extension-binding-v4-30.md`):
/// `--base lean-replay --root Init` over the v4.30.0-rc2 toolchain library
/// (1,770 modules, 63,363 constants) and `--root Mathlib.Order.Basic` over the
/// source-elab corpus (mathlib4 43ad0e9d; 6,822 modules) print these 41 rows
/// byte-identically. Every key's v4.30 definition was reviewed against the
/// toolchain's `src/lean/Init` for the meaning its hook assumes, and the
/// literal facts ground-truthed on the pinned `lean` binary (same report).
///
/// Re-minted 2026-10-19 (DECISIONS R150) when the `.olean` decoder began
/// keeping every stored `max`/`imax` level verbatim: `String`,
/// `String.ofList` and `autoParam` moved, because their cones hold
/// `List.brecOn.go`, whose stored level `max (max 1 u_1) (max (u+1) u_1)` the
/// old decoder collapsed to `max (u+1) u_1` (the same level at every
/// assignment); the other 38 rows are unchanged. Minted from the six key
/// modules by `extension_binding_lean_tests.rs`; reviewed in
/// `reports/2026-10-19-extension-binding-verbatim-levels.md`. The 2026-09-28
/// byte-identity over `Init` and `Mathlib.Order.Basic` above is of the rows
/// before this re-mint; the three moved rows were not re-measured over those
/// roots.
///
/// Re-minted 2026-11-14 (Q4 residuals, `docs/DECISIONS.md`) when the
/// fingerprint began erasing `MData` from ordinary constants (`fingerprint.rs`,
/// `Annotations`): the 23 keys whose ordinary cone carries a wrapper moved
/// (`Char`, `Char.ofNat`, `Int.add`, `Int.mul`, `Int.sub`, `Nat.add`, `Nat.beq`,
/// `Nat.ble`, `Nat.div`, `Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.mod`, `Nat.mul`,
/// `Nat.pow`, `Nat.pred`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.sub`,
/// `Nat.xor`, `String`, `String.ofList`, `autoParam`); the other 18 rows are
/// unchanged. That the moved rows are exactly those keys is a test
/// (`fingerprint_mdata_lean_tests.rs`), and so is the fenced kernel's reading
/// of each wrapped value as its body. No definition changed: the review of
/// 2026-09-28 and 2026-10-19 stands, now of the same terms with their
/// annotations erased. Minted from the six key modules by
/// `extension_binding_lean_tests.rs`.
#[rustfmt::skip]
const LEAN_V4_30_0_RC2: &[(&str, &str)] = &[
    ("Bool.false", "be3c3f6396fab9e977cfdb4222a39d021172bff22c7d4ad1733223908305813e"),
    ("Bool.true", "be3c3f6396fab9e977cfdb4222a39d021172bff22c7d4ad1733223908305813e"),
    ("Char", "c7f35a9f2e5d66be1c1f47e93910c8c5928ae4650bb235d9cdc4bbf5625c6e12"),
    ("Char.ofNat", "e63cf7f2f5fc960d4fcf25303aaa5ec7aff02e4b65704d36b6dc3a6b6aee9613"),
    ("Eq", "137a9846542d714510e3861e0086c1fb7be53bd46d706053d54264ede218069f"),
    ("Int", "c6e7343231f2ae48dfac2a151a7ce6b40086d3027392b4dfa990c166be8a9869"),
    ("Int.add", "0ebe89994b3a9e7845c7221ec12ebf092a0657d06f4a528a1ac6927cdd9fc219"),
    ("Int.mul", "8136941624c59c18813a44a8473eb65c542f1b7ba1ff81491bc12a86e2eb2979"),
    ("Int.negSucc", "c6e7343231f2ae48dfac2a151a7ce6b40086d3027392b4dfa990c166be8a9869"),
    ("Int.ofNat", "c6e7343231f2ae48dfac2a151a7ce6b40086d3027392b4dfa990c166be8a9869"),
    ("Int.rec", "c6e7343231f2ae48dfac2a151a7ce6b40086d3027392b4dfa990c166be8a9869"),
    ("Int.sub", "e1d744cd7228f96f2cd78f99e7c1e5cfd4a4fac1eba276692370851fc6027ae1"),
    ("Lean.reduceBool", "6be8176c6fdc1381b59e519880e69ec38971ead02b0e3c83d175aaa30d438b9a"),
    ("Lean.reduceNat", "2fe2ef294893b84d92a097839784a13ab0b9e5c0070162be8570fc4abdba9e88"),
    ("List.cons", "9d4c05548ea48d9614e5b99f7b29242067d6232eada9d0541af740f40b194b68"),
    ("List.nil", "9d4c05548ea48d9614e5b99f7b29242067d6232eada9d0541af740f40b194b68"),
    ("Nat", "97a4bfe636afd7e2bb7ec71fee26a2142b745a949fb6d29e8009a90eea3a2ca5"),
    ("Nat.add", "ef44e32635fe78f4ffc92c4b00e011b60c179560ef8eb236ee08f0a1f051d07e"),
    ("Nat.beq", "229a808bb6b897fe1ce1d7a3881c20c899d07c80c8acf9cc71c26b6e49a4177b"),
    ("Nat.ble", "5ef228aa81a23418efe1d3f1ee9dd4a85121fc595a89974a0c78ccd109529193"),
    ("Nat.div", "423d2d1f96c0947bb66eda6e75fffa0269f6386ab0928934fe84ff73567ec3cc"),
    ("Nat.gcd", "37fa623a88851db6f042950d34cc425fc88b8bc9717980bee8594c6e548aa89c"),
    ("Nat.land", "0df6d2102901ca7a633e37df5e877a0e91e957437b7d1a5bd0fe2bdcfe1173d8"),
    ("Nat.lor", "33f6600f90cba081a207da85d81e28f64707279f31b5bff2d989eadf4e0081d0"),
    ("Nat.mod", "746e448063023ed994c2c94d3128325bab40d580edb6b5d9d4b28e5af4c16e9d"),
    ("Nat.mul", "136d6b33064ab20b1732771951c62fddec4eb482240afec82d177e94fd7e39a1"),
    ("Nat.pow", "aa59492ce3c0a291bb9fe4d1238fe2edad84e31f0e4afde32e646c915ecd976d"),
    ("Nat.pred", "52a04ff0fbed5ddf88217892e7b2e3605dc3b0e59bf1fd92b0c89b4a28c3f78c"),
    ("Nat.rec", "97a4bfe636afd7e2bb7ec71fee26a2142b745a949fb6d29e8009a90eea3a2ca5"),
    ("Nat.shiftLeft", "a61cc8b4a77d931a267d4a8615fa6bd6634a14ac170c43fe7f0f266de818dca7"),
    ("Nat.shiftRight", "0c407d18d2e929548fce16843825f41f73880af5296c1ec4e976ae59d505c1d8"),
    ("Nat.sub", "dba7355f181e97a9867fcad95ab433f60ed2bfd8ba4e6edd0a4e0c122b40638e"),
    ("Nat.succ", "97a4bfe636afd7e2bb7ec71fee26a2142b745a949fb6d29e8009a90eea3a2ca5"),
    ("Nat.xor", "516030e2dfddf5f0aa4f3c8144b27d44d6caccdd4afd73476866d0a8f08c8d09"),
    ("Nat.zero", "97a4bfe636afd7e2bb7ec71fee26a2142b745a949fb6d29e8009a90eea3a2ca5"),
    ("String", "b00e12bbb030ec53623d6eb12b4514278208b9354ade6e2f85bee815e962541e"),
    ("String.ofList", "7efa20ace6688a87519c4aeab0ca6fca9d89a41b58d004119bf6e921765befe3"),
    ("autoParam", "1b8e66a0258bc33a03723b3fa76279eb70ba4158acd9f110456508db05853483"),
    ("optParam", "d36875cfbfeb0985d655497e0541dc038def771f74a4be30bd205f5f18e6a4ab"),
    ("outParam", "75fc9ffa3b4256dbd1b75f8f5ee23e379f17128ff4906c957cc8cde1d6628751"),
    ("semiOutParam", "888d5a2634e22b1b9ea6211e0b794baa559edb234a31a651eff5a9df96cf5a9a"),
];

/// `(name, fingerprint)` for the keys Lean v4.30.0-rc2's `Init` supplies ON TOP
/// OF the import-mode prelude (`Environment::try_with_prelude_for_import`), the
/// base `clean check --imports-prefer-olean`, `clean lake build` and `clean
/// project check` snapshot for their `ImportedConeGate`.
///
/// The importer keeps the FIRST declaration of a name, so in that environment
/// an imported key's cone reaches the prelude's own declaration wherever the
/// prelude declares the name too, and the fingerprint follows: `Nat.add`'s
/// matcher reaches `Nat.casesOn`, which the prelude holds as a kernel-built
/// eliminator of `Nat` and v4.30 as a definition over `Nat.rec`. Every such
/// divergence in these 23 cones was listed by a Merkle diff of the two worlds
/// and reviewed as a representation of the same function: kernel-built
/// `casesOn`/`rec` eliminators for Lean's `casesOn` definitions, level
/// parameters renamed, the `outParam` annotation absent on the heterogeneous
/// operator classes, eta-expanded projections, `p → False` for `¬p`, and
/// alternative defining terms for `Nat.pred`, `Bool.decEq`, `ite`,
/// `Decidable.decide`, `Bool.and`/`or`/`not`, `BEq.beq`, `Int.neg`, `Fin.val`
/// and `instDecidableAnd`/`Or` (the list and the review:
/// `reports/2026-09-28-extension-binding-v4-30.md`). The kernel's own
/// native-fold canon already pins this mixed world for the same heads
/// (`clean-import+lean-v4.30.0-rc2`, `clean-kernel/src/env/native_fold_canon.tsv`).
///
/// Keys the import prelude itself declares (`Nat`, `Nat.pred`, …,
/// `Eq`) have NO row: the gate takes the base as given, so they are never
/// gated there, and a row would vouch for the prelude's declaration under a
/// Lean world's name.
///
/// Measured 2026-09-28: `--base import-prelude --root Init` over the
/// v4.30.0-rc2 toolchain library and `--root Mathlib.Order.Basic` over the
/// source-elab corpus print these rows byte-identically.
///
/// Re-minted 2026-10-19 for the verbatim level decode (DECISIONS R150):
/// `String`, `String.ofList` and `autoParam` moved, for the same
/// `List.brecOn.go` level as in `LEAN_V4_30_0_RC2`; the other 20 rows are
/// unchanged. The 2026-09-28 byte-identity above is of the rows before this
/// re-mint; the three moved rows were minted from the key modules only and
/// were not re-measured over `Init` or `Mathlib.Order.Basic`.
/// Four rows added 2026-11-12 after removing the import base's value-free
/// bitwise placeholders and their Nat instances. All 23 previous rows are
/// unchanged. The four definitions already match the reviewed native-fold
/// authority rows; direct imported-helper replay and counterfeit/base-axiom
/// controls are recorded in `reports/cic-l-bitwise-base-2026-11-12/`.
///
/// Re-minted 2026-11-14 for the `MData` erasure (as in `LEAN_V4_30_0_RC2`):
/// 22 of the 27 rows moved, the same keys less `Nat.pred`, which this world
/// has no row for; `Lean.reduceBool`, `Lean.reduceNat`, `optParam`,
/// `outParam` and `semiOutParam` are unchanged. Minted from the key modules
/// by `extension_binding_lean_tests.rs`.
///
/// Re-minted 2026-11-14 for the prelude's `Not` restatement (4120bdd37:
/// `Decidable.isFalse : ¬p → Decidable p` and `Decidable.decide`'s isFalse
/// minor binder, stated with `Not` as pinned Lean states them), which landed
/// beside the `MData` re-mint above rather than under it. 11 rows moved
/// (`Char.ofNat`, `Nat.div`, `Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.mod`,
/// `Nat.shiftRight`, `Nat.xor`, `String`, `String.ofList`, `autoParam`),
/// and a dependency-closure probe over the six key modules on the import
/// prelude found exactly those 11 keys' cones reaching the prelude's
/// `Decidable.isFalse`; the other 16 reach none of the restated declarations
/// and are unchanged, and the empty-base world (no prelude) is unchanged.
/// `Not p` unfolds to `p → False`, so no definition's meaning changed: the
/// 2026-09-28 review of `p → False` for `¬p` stands. Minted from the key
/// modules by `extension_binding_lean_tests.rs`.
#[rustfmt::skip]
const CLEAN_IMPORT_LEAN_V4_30_0_RC2: &[(&str, &str)] = &[
    ("Char", "f9d9dae91229da08821e74a71bfe5f7e46f1d4cd5e5062107e43811e50728671"),
    ("Char.ofNat", "c29f4f995d49a56d8671cb8562063a8f8fc3a79ffbd3b21415281576bf73e3a2"),
    ("Int.add", "e601736562954f363248fc376524e5eb728a2c1af97253e65f016e98806c4823"),
    ("Int.mul", "184ee8dc5a1b257c7f78d6d5230fa2d45a05c4aa29e87582434c91efa7c2543c"),
    ("Int.sub", "d76a847f11badd02ebf2e7e5e6942306971db4234609060323983b88cc665563"),
    ("Lean.reduceBool", "6be8176c6fdc1381b59e519880e69ec38971ead02b0e3c83d175aaa30d438b9a"),
    ("Lean.reduceNat", "2fe2ef294893b84d92a097839784a13ab0b9e5c0070162be8570fc4abdba9e88"),
    ("Nat.add", "121c416efcb4c8eb5c4311fbc91015f4f25a70236acba778ada0d9f158df11f6"),
    ("Nat.beq", "83c39b49816d8e2e9ef0b74a8188e2597f098cd5551c8a1f37138f4299d7f3f8"),
    ("Nat.ble", "531f25bd8844675b83da3a517aeb22220b4f11c53b8d8c20fc35e2a3fdd701bb"),
    ("Nat.div", "84f3450c06874930f4e6f4503a5c9d16630c4ddde81e65eaa0fd7ba20af88986"),
    ("Nat.gcd", "2bddcc1798ed8526fe4fb19f965b7ec16d00b3fee2584341c43aaaebfb9bc0fe"),
    ("Nat.land", "3349e7b388e90e2a87a1a9ceb834dc9fcb98a0d2f30f38debff8e25d3cbbb617"),
    ("Nat.lor", "3673a32dc0c02f77df027917205d53fbcb5021487c73103e033988205aa48d16"),
    ("Nat.mod", "25f0117d9a63266a184ecee78dcb25fca8b0c853673f62406950dee8455e895a"),
    ("Nat.mul", "720970cb26db76731d9bec13253ccb67c29d382068e2840571255d29c0d9fefc"),
    ("Nat.pow", "edee52587c6ccd02c2d4cff279da5bd5a00928cdf7bac9228bf22d6b457fc875"),
    ("Nat.shiftLeft", "19696fcfe9b6ac5c2c6bcb517d1a5522b991a49b0bc1c170a4a95bd11bd7581a"),
    ("Nat.shiftRight", "81c2822df02b4381a2752ba7ba99093fea6806c705e784f2e5ee07f40bf0a0ce"),
    ("Nat.sub", "5e97e946f56ea44f0bf26073978184cf374871a437cb55de2963393a78e91413"),
    ("Nat.xor", "f306c9c11e01659abdf0b0dcea9a1f4f3504314607f2618db7796dc5e71cd4c1"),
    ("String", "a055d5a9f13ed9f4c662be37080755bfd81c1fa763e8dfa8b09cdc503b8edf0d"),
    ("String.ofList", "1b2d09f29bd6bf9c4172aaeedeb35e6f3dcaac59db57411e6a752a9b56d5cc75"),
    ("autoParam", "0fd2e9590c12ef456dc0ceb3993897619abb2aeaf6b12784a37036c790dcdf87"),
    ("optParam", "d36875cfbfeb0985d655497e0541dc038def771f74a4be30bd205f5f18e6a4ab"),
    ("outParam", "75fc9ffa3b4256dbd1b75f8f5ee23e379f17128ff4906c957cc8cde1d6628751"),
    ("semiOutParam", "888d5a2634e22b1b9ea6211e0b794baa559edb234a31a651eff5a9df96cf5a9a"),
];

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Claim c08 (F-064 / F-065): the canonical text format dropped fields
//! SILENTLY, so a text round trip could launder a refusal.
//!
//! Source: `reports/2026-09-17-two-language-proof-program/verify/c08_text_launders_refusals/`.
//! Each row prints a module with `format::canonical`, re-parses it with
//! `parser::parse_module`, and measures what survived. What the archive
//! measured:
//!
//! * `Module.global_asm` was dropped with no parse error (F-065). This was
//!   the one PERMISSIVE loss: `validate_module_for_codegen` refused the
//!   original (`GlobalAsmNotConsumable`) and accepted the text-tripped copy.
//! * `FunctionSummary` (and with it `proved` and `backed_by`) was dropped
//!   (F-064; conservative direction).
//! * a CleanCic certificate's `kernel_recheck` directive was dropped (fails
//!   closed: the module then loses its kernel tier).
//! * the v41 obligation kinds `termination` / `ownership` / `custom:` were
//!   printed but not parsed (a loud error).
//! * definition-site names outside the ASCII identifier alphabet were printed
//!   bare and not parsed (a loud error).
//!
//! WS4.2 (text fails closed until it is total) makes every one of these a
//! NAMED refusal: `format::text_losses` lists the field, `canonical_checked`
//! refuses, and the `canonical` image carries a `; #lossy:` marker the parser
//! refuses. So T1 — the permissive laundering — is CLOSED (its flipped twin is
//! conformance `text_losses`' `verify_c08_l1_*` and gate 11's
//! `b7.text.flip.*` rows), and since WS4.5 closed for good: text CARRIES the
//! block (`global_asm "<escaped>"`), so the refusal survives the round trip.
//! WS4.3 carried the quoted names, and WS4.4 carries the proof surface
//! (summaries with their `proved` bit and `backed_by` citation, kernel
//! re-check directives, the v41 kinds), so T2/T3/T4a land as their flipped
//! twins here (`c08_flipped_*`): each field now round-trips EXACTLY, and a
//! mutation control shows that dropping it from the text is what the old
//! grammar did. The `bydesign_*` row is a module that round-trips today and
//! must keep doing so.

use trust_ir::format::{NameKind, TextLoss};
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    CleanCicKernelRecheck, ObligationKind, ProofCertificate, ProofDigest, ProofEvidence,
    ProofFormula, ProofObligation, ProofStatus, clean_cic_lineage_digest,
};
use trust_ir::ty::{FieldDef, FuncTy, StructDef, Ty};
use trust_ir::value::{BlockId, FuncId, ProofId, StructId, ValueId};
use trust_ir::{
    Block, BodyGate, ExternRef, Function, FunctionSummary, Module, ModuleImport, Producer,
};

fn text_trip(m: &Module) -> Result<Module, String> {
    let text = trust_ir::format::canonical(m);
    trust_ir::parser::parse_module(&text).map_err(|e| format!("{e:?}"))
}

/// The text round trip is refused at the `; #lossy:` marker, which names
/// exactly `summary` (the parser's WS4.2 refusal).
fn assert_refused_as_lossy(m: &Module, summary: &str) {
    let err = text_trip(m).expect_err("a #lossy text must not parse");
    assert!(
        err.contains(&format!("this text was printed LOSSILY ({summary})"))
            && err.contains("re-emit from the binary/serde artifact"),
        "{err}"
    );
}

/// The `canonical` image with its `; #lossy:` marker deleted — what a human
/// who strips the tripwire would feed the parser.
fn unmarked_trip(m: &Module) -> Result<Module, String> {
    let text: String = trust_ir::format::canonical(m)
        .lines()
        .filter(|line| !line.starts_with("; #lossy:"))
        .map(|line| format!("{line}\n"))
        .collect();
    trust_ir::parser::parse_module(&text).map_err(|e| format!("{e:?}"))
}

/// `fn <name>(x: u64) -> u64 { x }`, producer TRust, Gated.
fn gated_identity(module: &str, name: &str) -> Module {
    let mut m = Module::new(module);
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), name, ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U64));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    f.blocks.push(block);
    f.producer = Some(Producer::TRust);
    f.body_gate = Some(BodyGate::Gated {
        authority: "verify-c08".into(),
        evidence: None,
    });
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

fn ensures_true() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(ProofFormula::smtlib2("(= 1 1)", "Bool"))
}

/// Row `verify.c08` T2/T2b, FLIPPED BY WS4.4 (F-064): a `proved` summary
/// `backed_by` an import was dropped whole with no parse error (and, under
/// WS4.2, refused as `#lossy: function-summary(fn 0)`). Text now CARRIES it —
/// `; #summary:` / `; #ensures:` / `; #backed-by:` — so the module round-trips
/// exactly, claim and citation included. Mutation control: the same text with
/// the summary block deleted parses to a module WITHOUT the summary, which is
/// exactly the drop the old grammar performed.
#[test]
fn c08_flipped_text_carries_function_summary_and_backed_by() {
    let mut m = gated_identity("c08_importer", "g");
    let id = m
        .intern_import(
            ModuleImport::new("c08_dep", ProofDigest::sha256([0x11; 32]))
                .with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    m.functions[0].summary = Some(
        ensures_true()
            .proved()
            .backed_by(ExternRef::new(id, "g").relying_on(ProofId::new(0))),
    );
    assert_eq!(trust_ir::format::text_losses(&m), vec![]);
    let back = text_trip(&m).expect("the summary is carried");
    assert_eq!(back, m);
    assert_eq!(back.stable_digest(), m.stable_digest());
    let summary = back.functions[0].summary.as_ref().unwrap();
    assert!(summary.proved && summary.backed_by.is_some());
    // Mutation control: delete the block, and the claim and citation vanish.
    let dropped: String = trust_ir::format::canonical(&m)
        .lines()
        .filter(|line| {
            !["#summary:", "#ensures:", "#backed-by:"]
                .iter()
                .any(|word| line.contains(word))
        })
        .map(|line| format!("{line}\n"))
        .collect();
    let edited = trust_ir::parser::parse_module(&dropped).expect("parses");
    assert!(edited.functions[0].summary.is_none());
    assert_ne!(edited.stable_digest(), m.stable_digest());
}

/// Row `verify.c08` T3, FLIPPED BY WS4.4 (F-070): a CleanCic certificate's
/// `kernel_recheck` directive was dropped (so the text-tripped module lost its
/// kernel tier — fail-closed; under WS4.2 a named `#lossy` refusal). Text now
/// CARRIES it as a trailing `recheck module .. anchor .. theorems [..] axioms
/// [..]` clause, so the certificate round-trips exactly. Mutation control:
/// cutting the clause from the text yields the directive-less certificate the
/// old grammar produced.
#[test]
fn c08_flipped_text_carries_kernel_recheck_directive() {
    let mut m = gated_identity("c08_cic", "addmul");
    let ob = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::TranslationValidation,
        ProofStatus::Certified,
        "backend translation validation",
    )
    .with_function(FuncId::new(0));
    m.proof_certificates.push(ProofCertificate {
        obligation: ob.id,
        prover: "clean-backend-tv".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![1, 2, 3],
            context: vec![4, 5, 6],
            lineage: clean_cic_lineage_digest(&ob),
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "CleanCompiler.BackendTV".into(),
                theorems: vec!["CleanTV.addmul.denotes".into()],
                anchor: "clean_backend_tv".into(),
                allowed_axioms: vec![],
                binding: None,
            }),
        },
        assurance: None,
    });
    m.proof_obligations.push(ob);
    assert_eq!(trust_ir::format::text_losses(&m), vec![]);
    let back = text_trip(&m).expect("the directive is carried");
    assert_eq!(back, m);
    let text = trust_ir::format::canonical(&m);
    let cut = text.find(" recheck module ").expect("the recheck clause");
    let end = cut + text[cut..].find('\n').expect("line end");
    let dropped = format!("{}{}", &text[..cut], &text[end..]);
    let edited = trust_ir::parser::parse_module(&dropped).expect("parses");
    assert!(matches!(
        &edited.proof_certificates[0].evidence,
        ProofEvidence::CleanCic {
            kernel_recheck: None,
            ..
        }
    ));
}

fn with_obligation(kind: ObligationKind) -> Module {
    let mut m = gated_identity("c08_kinds", "id");
    m.proof_obligations.push(
        ProofObligation::new(ProofId::new(0), kind, ProofStatus::Pending, "probe")
            .with_function(FuncId::new(0)),
    );
    m
}

/// Row `verify.c08` T4a, FLIPPED BY WS4.4 (F-071): `termination`,
/// `ownership` and `custom:<ns>/<name>` were printed but refused by the parser
/// as unknown kinds (under WS4.2, refused at print time). The parser now reads
/// all three; `Custom` has the module-text spelling `custom("<ns>", "<name>")`
/// because its diagnostic `Display` form is not injective. Mutation control:
/// the diagnostic spelling pasted into module text is still refused.
#[test]
fn c08_flipped_v41_obligation_kinds_parse() {
    for (kind, spelled) in [
        (ObligationKind::Termination, "termination".to_string()),
        (ObligationKind::Ownership, "ownership".to_string()),
        (
            ObligationKind::Custom {
                namespace: "trust.vc".into(),
                name: "probe".into(),
            },
            "custom(\"trust.vc\", \"probe\")".to_string(),
        ),
    ] {
        let m = with_obligation(kind.clone());
        assert_eq!(trust_ir::format::text_losses(&m), vec![], "{kind}");
        let text = trust_ir::format::canonical(&m);
        assert!(
            text.contains(&format!("obligation 0 {spelled} pending")),
            "{text}"
        );
        assert_eq!(text_trip(&m).expect("the kind parses"), m, "{kind}");
    }
    let custom = with_obligation(ObligationKind::Custom {
        namespace: "trust.vc".into(),
        name: "probe".into(),
    });
    let diagnostic = trust_ir::format::canonical(&custom).replacen(
        "custom(\"trust.vc\", \"probe\")",
        "custom:trust.vc/probe",
        1,
    );
    assert!(trust_ir::parser::parse_module(&diagnostic).is_err());
}

fn with_names(func: &str, strukt: &str) -> Module {
    let mut m = gated_identity("c08_names", func);
    m.add_struct(StructDef {
        id: StructId::new(0),
        name: strukt.into(),
        // Keep the field unnamed so these rows isolate definition-site names.
        // WS4.5 also carries named fields and explicit offsets losslessly.
        fields: vec![FieldDef {
            name: String::new(),
            ty: Ty::U64,
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    m
}

const DEFINITION_NAME_KINDS: [NameKind; 7] = [
    NameKind::Function,
    NameKind::Global,
    NameKind::Struct,
    NameKind::Enum,
    NameKind::EnumVariant,
    NameKind::Record,
    NameKind::RecordField,
];

fn definition_names_module() -> Module {
    let mut module = gated_identity("definition_names", "before_function");
    let mut function = module.functions[0].clone();
    function.id = FuncId::new(1);
    function.name = "after_function".into();
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    for index in 0..2 {
        module.add_struct(StructDef {
            id: StructId::new(index),
            name: format!("Struct{index}"),
            fields: vec![],
            size: Some(0),
            align: Some(1),
            repr: Default::default(),
            origin: None,
        });
        module.add_enum(trust_ir::EnumDef::new(
            trust_ir::EnumId::new(index),
            format!("Enum{index}"),
            vec![trust_ir::EnumVariant {
                name: "Variant".into(),
                fields: vec![],
                field_names: vec![],
            }],
        ));
        module.add_record(trust_ir::RecordDef {
            id: trust_ir::RecordId::new(index),
            name: format!("Record{index}"),
            fields: vec![FieldDef {
                name: "field".into(),
                ty: Ty::U64,
                offset: None,
            }],
        });
        module.globals.push(trust_ir::Global {
            name: format!("global{index}"),
            ty: Ty::U64,
            mutable: false,
            initializer: Some(trust_ir::Constant::Int(0)),
            linkage: trust_ir::Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
    }
    module
}

fn definition_name(module: &mut Module, kind: NameKind) -> &mut String {
    // The second table row checks that the loss names the owning definition's
    // position. Nested variant/field index zero must not replace that position.
    match kind {
        NameKind::Function => &mut module.functions[1].name,
        NameKind::Global => &mut module.globals[1].name,
        NameKind::Struct => &mut module.structs[1].name,
        NameKind::Enum => &mut module.enums[1].name,
        NameKind::EnumVariant => &mut module.enums[1].variants[0].name,
        NameKind::Record => &mut module.records[1].name,
        NameKind::RecordField => &mut module.records[1].fields[0].name,
        _ => unreachable!("the matrix contains only definition-site names"),
    }
}

#[test]
fn c08_empty_definition_names_are_named_refusals() {
    for kind in DEFINITION_NAME_KINDS {
        let mut module = definition_names_module();
        definition_name(&mut module, kind).clear();
        let expected = vec![TextLoss::UnspellableName { kind, index: 1 }];
        assert_eq!(trust_ir::format::text_losses(&module), expected, "{kind:?}");
        assert_eq!(
            trust_ir::format::canonical_checked(&module).map_err(|error| error.losses),
            Err(expected.clone()),
            "{kind:?}"
        );
        assert_refused_as_lossy(&module, &expected[0].to_string());
        let unmarked: String = trust_ir::format::canonical(&module)
            .lines()
            .filter(|line| !line.starts_with("; #lossy:"))
            .map(|line| format!("{line}\n"))
            .collect();
        let error = trust_ir::parser::parse_module(&unmarked).unwrap_err();
        assert_eq!(error.message, "empty symbol", "{kind:?}: {error:?}");
    }
}

#[test]
fn c08_nonempty_definition_names_remain_lossless() {
    for kind in DEFINITION_NAME_KINDS {
        // Whitespace and control characters are nonempty names too. They must
        // keep the quoted spelling, without trimming or a restored bare-only gate.
        for name in ["plain_name", " ", "café::Type<\"T\">", "\0\n"] {
            let mut module = definition_names_module();
            *definition_name(&mut module, kind) = name.into();
            assert!(
                trust_ir::format::text_losses(&module).is_empty(),
                "{kind:?}"
            );
            let text = trust_ir::format::canonical_checked(&module).unwrap();
            assert!(!text.contains("; #lossy:"), "{kind:?}: {text}");
            assert_eq!(
                trust_ir::parser::parse_module(&text).unwrap(),
                trust_ir::format::canonicalize(&module),
                "{kind:?}: {name:?}"
            );
        }
    }
}

#[test]
fn c08_empty_module_name_remains_a_lossless_string() {
    let module = Module::new("");
    let text = trust_ir::format::canonical_checked(&module).unwrap();
    assert_eq!(trust_ir::parser::parse_module(&text).unwrap(), module);
}

/// Row `verify.c08` T4b, FLIPPED BY WS4.3: def-path and generic spellings of a
/// function or struct name are no longer a text loss — the printer spells them
/// quoted (`@"krate::foo"`) and `Parser::read_symbol` decodes them, so the
/// module round-trips. Before WS4.3 each was a `TextLoss::UnspellableName`, the
/// whole module was refused at print time via the `#lossy` marker, and the
/// marker-deleted copy still failed to parse.
#[test]
fn c08_names_outside_the_identifier_alphabet_round_trip_quoted() {
    for (func, strukt) in [
        ("krate::foo", "Pair"),
        ("foo\'", "Pair"),
        ("foo<u64>", "Pair"),
        ("foo::{closure#0}", "Pair"),
        ("id", "core::option::Pair"),
        ("id", "Vec<u8>"),
        ("id", "Pair of"),
        // The shadowing spelling that made 98 of 152 battery text losses.
        ("m::wsum::<shadowed-by-clean-origin:FuncId(4)>", "Pair"),
    ] {
        let m = with_names(func, strukt);
        assert_eq!(
            trust_ir::format::text_losses(&m),
            vec![],
            "no name is a text loss after WS4.3: {func} / {strukt}"
        );
        assert!(text_trip(&m).is_ok(), "{func} / {strukt}");
        assert!(unmarked_trip(&m).is_ok(), "{func} / {strukt}");
    }
}

/// WS4.3 ONE-SPELLING RULE (SPEC §3): a name inside the bare alphabet MUST be
/// spelled bare, so parse stays a bijection on printer output. The printer never
/// emits the quoted form for such a name, and the parser REFUSES it — otherwise
/// two different texts would denote the same module.
#[test]
fn c08_ws43_bare_able_name_is_printed_bare_and_its_quoted_spelling_is_refused() {
    let m = with_names("plain_name", "Pair");
    let text = trust_ir::format::canonical(&m);
    assert!(
        text.contains("fn @plain_name("),
        "a bare-able name must print bare:\n{text}"
    );
    assert!(
        !text.contains("@\"plain_name\""),
        "a bare-able name must NOT print quoted:\n{text}"
    );
    let quoted = text.replace("fn @plain_name(", "fn @\"plain_name\"(");
    let err = trust_ir::parser::parse_module(&quoted)
        .expect_err("the quoted spelling of a bare-alphabet name is refused");
    assert!(
        format!("{err}").contains("must be spelled bare"),
        "refusal must name the rule: {err}"
    );
}

/// Positive fixture and mutation controls: a module with nothing text-lossy
/// keeps its digest; the `liveness` kind round-trips; mangled, `$`-bearing
/// and dotted Clean names round-trip.
#[test]
fn c08_bydesign_lossless_module_kinds_and_names_round_trip() {
    let m = gated_identity("c08_control", "id");
    assert!(trust_ir::format::canonical_checked(&m).is_ok());
    let back = text_trip(&m).expect("parses");
    assert_eq!(back.stable_digest(), m.stable_digest());

    let live = with_obligation(ObligationKind::Liveness);
    let back = text_trip(&live).expect("liveness parses");
    assert_eq!(back.proof_obligations[0].kind, ObligationKind::Liveness);

    for name in [
        "_RNvCs1234_5crate3foo",
        "_ZN5crate3foo17h0123456789abcdefE",
        "_$LT$T$u20$as$GT$",
        "Nat.add",
    ] {
        let named = with_names(name, "Pair");
        assert!(
            trust_ir::format::canonical_checked(&named).is_ok(),
            "{name}"
        );
        let back = text_trip(&named).expect(name);
        assert_eq!(back.functions[0].name, name);
    }
}

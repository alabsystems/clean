// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Raw transport owns the complete positional ABI table, including its empty
//! tail. Canonicalization remains an explicit, separate transformation.

use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, ParamAttrs, Ty, ValueId,
};

fn owner(params: Vec<ParamAttrs>) -> Module {
    let mut module = Module::new("param_attrs");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr; 4],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    // Noncanonical SSA ids ensure this is raw transport, not a canonicalized
    // proxy whose slot table or source body has been rewritten first.
    let mut function = Function::new(FuncId::new(0), "slots", signature, BlockId::new(7));
    let mut block = Block::new(BlockId::new(7));
    block.params = [11, 14, 17, 20]
        .into_iter()
        .map(|id| (ValueId::new(id), Ty::Ptr))
        .collect();
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    function.attrs.params = params;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn exact_roundtrip(module: &Module) -> String {
    let retained = module.clone();
    let bytes = serialize_module(module).expect("serialize_module: test fixture");
    assert!(trust_ir::text_loss::text_losses(module).is_empty());
    let text = trust_ir::format::text_checked(module).expect("raw lossless text");
    assert!(!text.contains("#lossy"), "{text}");
    let parsed = trust_ir::parser::parse_module(&text).expect("parse actual raw spelling");
    assert_eq!(
        &parsed, module,
        "every stored field remains owned by the producer"
    );
    assert_eq!(
        serialize_module(&parsed).expect("serialize_module: test fixture"),
        bytes,
        "raw binary custody is unchanged"
    );
    assert_eq!(deserialize_module(&bytes).unwrap(), *module);
    assert_eq!(trust_ir::format::text_checked(&parsed).unwrap(), text);
    assert_eq!(
        *module, retained,
        "printing must not mutate the source owner"
    );
    text
}

fn rows(text: &str) -> Vec<&str> {
    text.lines()
        .map(str::trim)
        .filter(|line| line.starts_with("; #param_attrs"))
        .collect()
}

#[test]
fn final_empty_parameter_row_is_carried_with_earlier_sret() {
    let module = owner(vec![
        ParamAttrs {
            sret: true,
            ..Default::default()
        },
        ParamAttrs::default(),
    ]);
    let text = exact_roundtrip(&module);
    assert_eq!(rows(&text), ["; #param_attrs 0: sret", "; #param_attrs 1:"]);
    // The old printer handed back this DIFFERENT owner; fact preservation is
    // not enough to claim a lossless structural artifact.
    let mut shortened = module.clone();
    shortened.functions[0].attrs.params.pop();
    assert_ne!(
        serialize_module(&shortened).expect("serialize_module: test fixture"),
        serialize_module(&module).expect("serialize_module: test fixture")
    );
}

#[test]
fn sparse_interior_rows_and_multiple_default_tail_slots_keep_exact_length() {
    let module = owner(vec![
        ParamAttrs::default(),
        ParamAttrs {
            byval: true,
            ..Default::default()
        },
        ParamAttrs::default(),
        ParamAttrs::default(),
    ]);
    let text = exact_roundtrip(&module);
    assert_eq!(
        rows(&text),
        ["; #param_attrs 1: byval", "; #param_attrs 3:"]
    );
    let canonical = trust_ir::format::canonicalize(&module);
    assert_eq!(canonical.functions[0].attrs.params.len(), 2);
    assert_eq!(module.functions[0].attrs.params.len(), 4);
    assert_eq!(
        canonical.functions[0].attrs.params[1],
        module.functions[0].attrs.params[1]
    );
}

#[test]
fn all_default_parameter_table_is_not_an_absent_table() {
    let module = owner(vec![ParamAttrs::default(); 4]);
    assert!(
        module.functions[0].attrs.is_empty(),
        "no slot fact is fabricated"
    );
    let text = exact_roundtrip(&module);
    assert_eq!(rows(&text), ["; #param_attrs 3:"]);
    assert_eq!(
        trust_ir::format::canonicalize(&module).functions[0]
            .attrs
            .params
            .len(),
        0
    );
    assert_ne!(
        serialize_module(&module).expect("serialize_module: test fixture"),
        serialize_module(&owner(vec![])).expect("serialize_module: test fixture")
    );
}

#[test]
fn empty_parameter_table_emits_no_slot_directive() {
    let module = owner(vec![]);
    assert!(rows(&exact_roundtrip(&module)).is_empty());
}

#[test]
fn independently_spelled_empty_tail_reconstructs_the_complete_actual_table() {
    // This syntax was already accepted by the reader. The producer must use
    // it, rather than erase defaults or suppress the loss marker artificially.
    let text = r#"module "param_attrs"
functy.0 = (ptr, ptr, ptr, ptr) -> ()
fn @slots(functy.0) {
    ; #param_attrs 0: sret
    ; #param_attrs 3:
bb7(%11: ptr, %14: ptr, %17: ptr, %20: ptr):
    ret
}
"#;
    let expected = owner(vec![
        ParamAttrs {
            sret: true,
            ..Default::default()
        },
        ParamAttrs::default(),
        ParamAttrs::default(),
        ParamAttrs::default(),
    ]);
    let parsed = trust_ir::parser::parse_module(text).expect("the pre-existing empty-row grammar");
    assert_eq!(parsed, expected);
    assert_eq!(
        serialize_module(&parsed).expect("serialize_module: test fixture"),
        serialize_module(&expected).expect("serialize_module: test fixture")
    );
}

#[test]
fn legacy_loss_markers_and_unknown_slot_attributes_still_refuse() {
    let module = owner(vec![ParamAttrs::default()]);
    let text = exact_roundtrip(&module);
    let marked = format!("; #lossy: param-attrs-tail(fn 0)\n{text}");
    let error =
        trust_ir::parser::parse_module(&marked).expect_err("old lossy artifacts stay refused");
    assert!(error.message.contains("printed LOSSILY"), "{error:?}");
    let malformed = text.replace("; #param_attrs 0:", "; #param_attrs 0: invented");
    let error =
        trust_ir::parser::parse_module(&malformed).expect_err("no permissive attribute fallback");
    assert!(error.message.contains("unknown param attr"), "{error:?}");
    let mut other_loss = module;
    other_loss.functions[0].name.clear();
    assert!(
        trust_ir::text_loss::text_losses(&other_loss)
            .iter()
            .any(|loss| matches!(loss, trust_ir::text_loss::TextLoss::UnspellableName { .. }))
    );
    assert!(trust_ir::format::text_checked(&other_loss).is_err());
    assert!(trust_ir::parser::parse_module(&other_loss.to_string()).is_err());
}

use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId};
use trust_ir::{Block, Function, Global, Linkage, Module, Visibility};

fn body(m: &mut Module, name: &str, lk: Linkage, naked: bool, feats: &[&str]) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(m.functions.len() as u32), name, ft, BlockId(0));
    f.linkage = lk;
    f.attrs.naked = naked;
    f.attrs.target_features = feats.iter().map(|s| s.to_string()).collect();
    let mut b = Block::new(BlockId(0));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

#[test]
fn v41_abi_residue_round_trips_all_four_formats() {
    let mut m = Module::new("abi");
    body(&mut m, "plain", Linkage::External, false, &[]);
    body(&mut m, "avail", Linkage::AvailableExternally, false, &[]);
    body(&mut m, "extweak", Linkage::ExternalWeak, false, &[]);
    body(&mut m, "wodr", Linkage::WeakOdr, true, &[]);
    body(
        &mut m,
        "lodr",
        Linkage::LinkOnceOdr,
        false,
        &["neon", "aes"],
    );

    m.globals.push(Global {
        name: "REGISTRY".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: Some(16),
        section: Some("__DATA,__mysection".into()),
        visibility: Visibility::Hidden,
        retained: true,
    });
    m.global_asm.push(".globl _start\n_start:\n  ret\n".into());

    let back = deserialize_module(&serialize_module(&m).expect("serialize_module: test fixture"))
        .expect("binary");
    assert_eq!(back, m, "binary");
    assert_eq!(back.globals[0].visibility, Visibility::Hidden);
    assert!(back.globals[0].retained);
    assert_eq!(back.global_asm.len(), 1);

    // Global symbol attributes AND (since WS4.5) global assembly survive
    // text: the whole residue round-trips exactly.
    let carried = m.clone();
    let text = trust_ir::format::canonical_checked(&carried).expect("loss-free");
    assert!(text.contains("global_asm \".globl _start\\n_start:\\n  ret\\n\"\n"));
    let re = trust_ir::parser::parse_module(&text).expect("text parses");
    assert_eq!(re, trust_ir::format::canonicalize(&carried));
    assert_eq!(re.globals, m.globals);
    // The four v41 linkages must survive `is_func_prefix` — a miss there
    // SILENTLY DROPS the function rather than erroring.
    assert_eq!(
        re.functions.len(),
        5,
        "no function may be dropped by the header scanner"
    );
    assert_eq!(re.functions[3].linkage, Linkage::WeakOdr);
    assert!(
        re.functions[3].attrs.naked,
        "naked must survive the text round-trip"
    );
    assert_eq!(re.functions[4].attrs.target_features, vec!["neon", "aes"]);

    let j = serde_json::to_string(&m).unwrap();
    assert_eq!(serde_json::from_str::<Module>(&j).unwrap(), m, "json");
    let mp = rmp_serde::to_vec(&m).unwrap();
    assert_eq!(
        rmp_serde::from_slice::<Module>(&mp).unwrap(),
        m,
        "positional msgpack"
    );
}

// Copyright 2026 Andrew Yates. Apache-2.0.
//! Propose an untrusted original-SemR proof for actual typed module bytes.
//! `--fixture` exercises transport only and makes no Rust-source proof claim.
use std::error::Error;
use std::path::Path;
use trust_ir::semr_bool_body::BoolBodyReader;
use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId};

fn fixture() -> Result<Module, Box<dyn Error>> {
    let mut module = Module::new("native-conjunction-fixture");
    let signature = module.add_func_type(FuncTy::unrecorded(
        vec![Ty::Bool, Ty::Bool],
        vec![Ty::Bool],
        false,
    ))?;
    let mut function = Function::new(FuncId::new(0), "conjunction", signature, BlockId::new(3));
    let mut block = Block::new(BlockId::new(3))
        .with_param(ValueId::new(7), Ty::Bool)
        .with_param(ValueId::new(11), Ty::Bool);
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: trust_ir::BinOp::And,
            ty: Ty::Bool,
            lhs: ValueId::new(7),
            rhs: ValueId::new(11),
        })
        .with_result(ValueId::new(19)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(19)],
    }));
    function.blocks.push(block);
    module.try_add_function(function)?;
    Ok(module)
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() < 2 {
        return Err("usage: semr_bool_body_candidate <module.tmbc|--fixture> <output-dir> [function-id ...]".into());
    }
    let output = Path::new(&args[1]);
    std::fs::create_dir_all(output)?;
    let (module, bytes, ids) = if args[0] == "--fixture" {
        eprintln!(
            "FIXTURE ONLY: native typed-IR transport; no Rust-source or compiler proof claim"
        );
        let module = fixture()?;
        let bytes = trust_ir::binary::serialize_module(&module)?;
        std::fs::write(output.join("subject.tmbc"), &bytes)?;
        (module, bytes, vec![FuncId::new(0)])
    } else {
        let bytes = std::fs::read(&args[0])?;
        let module = trust_ir::binary::deserialize_module(&bytes)
            .map_err(|error| std::io::Error::other(format!("{error:?}")))?;
        let ids = args[2..]
            .iter()
            .map(|id| id.parse().map(FuncId::new))
            .collect::<Result<Vec<_>, _>>()?;
        (module, bytes, ids)
    };
    let source = BoolBodyReader::new(&module)
        .candidate_source(&bytes, &ids)
        .map_err(|refusal| format!("pending body input refused: {refusal:?}"))?;
    std::fs::write(output.join("SemRBoolBodyCandidate.lean"), source)?;
    let originals = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../lean/semr")
        .canonicalize()?;
    let mut sources: Vec<_> = ["SemR", "SemRBoolBody", "SemRBoolWholeBody", "SemRBoolBodyChecker"].into_iter()
        .map(|module| serde_json::json!({"module":module,"path":originals.join(format!("{module}.lean"))})).collect();
    sources.push(
        serde_json::json!({"module":"SemRBoolBodyCandidate","path":"SemRBoolBodyCandidate.lean"}),
    );
    let mut roots = vec!["SemR.BoolBody.checked_blob".to_string()];
    let mut positive = Vec::new();
    let mut negative = Vec::new();
    for id in ids {
        let proof = format!("SemR.BoolBodyCandidate.correct_{}", id.index());
        roots.push(proof.clone());
        roots.push(format!(
            "SemR.BoolBodyCandidate.wrong_counterexample_{}",
            id.index()
        ));
        positive.push(serde_json::json!({"proof":proof,"goal":format!("SemR.BoolBodyCandidate.AndGoal_{}",id.index())}));
        negative.push(serde_json::json!({"proof":proof,"goal":format!("SemR.BoolBodyCandidate.OrGoal_{}",id.index())}));
    }
    let manifest = serde_json::json!({"sources":sources,"module":"SemRBoolBodyCandidate","roots":roots,"positive":positive,"negative":negative});
    std::fs::write(
        output.join("subject.json"),
        serde_json::to_vec_pretty(&manifest)?,
    )?;
    eprintln!(
        "UNTRUSTED candidate: {}",
        output.join("subject.json").display()
    );
    Ok(())
}

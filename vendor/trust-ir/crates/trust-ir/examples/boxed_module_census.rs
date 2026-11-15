// Copyright 2026 Andrew Yates | Apache-2.0
//! Lossless full-module census. Requires features `binary,serde`.
use sha2::{Digest, Sha256};
use std::{env, fs};
use trust_ir::binary;

fn main() {
    let path = env::args().nth(1).expect("module.bin path");
    let bytes = fs::read(path).expect("read complete binary");
    let module = binary::deserialize_module(&bytes).expect("maintained full decoder");
    let encoded = binary::serialize_module(&module).expect("full module encodable");
    let restored = binary::deserialize_module(&encoded).expect("decode full round trip");
    assert_eq!(module, restored, "no selected-only projection");
    let addresses: Vec<_> = module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id.index(), 4096 + 8 * i as u64))
        .collect();
    let body_digests: Vec<_> = module
        .functions
        .iter()
        .map(|f| (f.id.index(), module.function_body_digest(f.id)))
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "input_bytes": bytes.len(), "input_sha256": format!("{:x}", Sha256::digest(&bytes)),
            "roundtrip_lossless": true, "roundtrip_byte_identical": bytes == encoded,
            "synthetic_model_addresses_not_physical_abi": addresses,
            "function_body_digests": body_digests, "complete_module": module
        }))
        .unwrap()
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Explicit developer utility for registering and verifying the native
//! `nnverify_ieee754` shard.
//!
//! Usage:
//! `cargo run -p clean-mathverse --example register_nnverify_ieee754_shard -- \
//! /path/to/mathverse-library`
//!
//! The destination is mandatory; this utility never implicitly mutates the
//! repository. Registration is successful only if the emitted shard replays
//! cleanly through the kernel verifier.

use std::error::Error;
use std::path::PathBuf;

use clean_mathverse::nnverify_ieee754_shard::{
    register_nnverify_ieee754_shard, verify_nnverify_ieee754_shard, NNVERIFY_IEEE754_SHARD_NAME,
    NNVERIFY_IEEE754_SHARD_SUBDIR,
};

fn main() -> Result<(), Box<dyn Error>> {
    let root = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .expect("usage: register_nnverify_ieee754_shard /path/to/mathverse-library");
    let registration = register_nnverify_ieee754_shard(&root)?;
    let shard_path = root
        .join(NNVERIFY_IEEE754_SHARD_SUBDIR)
        .join(format!("{NNVERIFY_IEEE754_SHARD_NAME}.mathverse"));
    let verification = verify_nnverify_ieee754_shard(&shard_path)?;

    println!(
        "REGISTERED path={} hash={} constants={} exprs={}",
        registration.entry.path,
        registration.entry.content_hash,
        registration.entry.constant_count,
        registration.entry.expr_count
    );
    println!(
        "VERIFY total={} rechecked={} empty_closure_verified={} clean={}",
        verification.total,
        verification.kernel_rechecked,
        verification.empty_closure_verified.len(),
        verification.is_clean()
    );
    assert!(
        verification.is_clean(),
        "registered IEEE-754 shard failed kernel replay"
    );
    Ok(())
}

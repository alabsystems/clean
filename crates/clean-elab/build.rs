// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

fn main() {
    // Only the stable handshake is a build-script input. A participating host
    // must not expand (and therefore fingerprint) the legacy build-ID macro.
    println!("cargo:rerun-if-env-changed=CFG_TRUST_ORACLE_HOST");
    println!("cargo:rustc-check-cfg=cfg(clean_runtime_oracle_host)");
    if std::env::var_os("CFG_TRUST_ORACLE_HOST").is_some() {
        println!("cargo:rustc-cfg=clean_runtime_oracle_host");
    }
}

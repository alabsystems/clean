// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! .olean Binary Format Deserializer Fuzz Target
//!
//! Fuzzes `parse_header`, `parse_imports_only`, and `parse_module` with random
//! byte sequences. These functions parse untrusted binary data from Mathlib
//! .olean files and must never panic on malformed input.

#![no_main]

use clean_olean::{parse_header, parse_imports_only, parse_module};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Header parser — validates magic bytes, version, git hash
    let _ = parse_header(data);

    // Import-only parser — header + partial region read
    let _ = parse_imports_only(data);

    // Full module parser — header + compacted region + all constants
    let _ = parse_module(data);
});

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lean 4 Syntax Parser Fuzz Target
//!
//! Fuzzes `parse_file`, `parse_decl`, and `parse_expr` with random byte
//! sequences interpreted as UTF-8. The parser must never panic on arbitrary
//! input — it should return `Result` with an appropriate `ParseError`.

#![no_main]

use clean_parser::{parse_decl, parse_expr, parse_file};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Parser expects &str — skip non-UTF8 input
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return,
    };

    // Exercise all three parser entry points. Each must return Result, never panic.
    let _ = parse_file(input);
    let _ = parse_decl(input);
    let _ = parse_expr(input);
});

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::Interpreter;
use clean_kernel::sem_memory_model::{MemoryModel, MemoryValue};
use proptest::prelude::*;
use std::collections::HashSet;

fn shared_memory_value() -> impl Strategy<Value = MemoryValue> {
    any::<u8>().prop_map(MemoryValue::new)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn prop_memory_model_write_then_read_roundtrips(
        size in 1usize..8,
        value in shared_memory_value(),
    ) {
        let mut interpreter = Interpreter::new();
        let addr = interpreter
            .allocate(size)
            .expect("shared memory allocation should succeed");

        interpreter
            .write(addr, 0, value)
            .expect("write to fresh shared memory allocation should succeed");

        prop_assert_eq!(
            interpreter
                .read(addr, 0)
                .expect("read after write should succeed"),
            value
        );
    }

    #[test]
    fn prop_memory_model_allocate_returns_unique_addresses(
        sizes in proptest::collection::vec(0usize..8, 1..16),
    ) {
        let mut interpreter = Interpreter::new();
        let mut seen = HashSet::new();

        for size in sizes {
            let addr = interpreter
                .allocate(size)
                .expect("shared memory allocation should succeed");
            prop_assert!(seen.insert(addr));
        }
    }

    #[test]
    fn prop_memory_model_free_then_read_errors(
        size in 1usize..8,
        value in shared_memory_value(),
    ) {
        let mut interpreter = Interpreter::new();
        let addr = interpreter
            .allocate(size)
            .expect("shared memory allocation should succeed");

        interpreter
            .write(addr, 0, value)
            .expect("write to fresh shared memory allocation should succeed");
        interpreter
            .free(addr)
            .expect("free of live shared memory allocation should succeed");

        prop_assert!(!interpreter.is_valid(addr));
        prop_assert!(interpreter.read(addr, 0).is_err());
    }
}

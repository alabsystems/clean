// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

struct Counter {
    value: u32,
}

fn increment(c: &mut Counter) {
    c.value = c.value + 1u32;
}

fn main() -> u32 {
    let mut counter = Counter { value: 0u32 };
    let a: &mut Counter = &mut counter;
    let b: &mut Counter = &mut counter;
    increment(a);
    increment(b);
    counter.value
}

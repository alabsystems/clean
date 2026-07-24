// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

struct Sensor {
    reading: u32,
}

fn main() -> u32 {
    let mut sensor = Sensor { reading: 42u32 };
    let raw: *mut u32 = &mut sensor.reading as *mut u32;
    let shared: &u32 = &sensor.reading;
    unsafe {
        *raw = 99u32;
    }
    *shared
}

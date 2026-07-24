// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

enum Packet {
    Small { payload: u32 },
    Large { header: u32, body: u32 },
}

fn process(packet: Packet) -> u32 {
    match packet {
        Packet::Small { payload } => payload * 2u32,
        Packet::Large { header, body } => header + body,
    }
}

fn total(a: Packet, b: Packet) -> u32 {
    process(a) + process(b)
}

fn main() -> u32 {
    let small = Packet::Small { payload: 5u32 };
    let large = Packet::Large {
        header: 3u32,
        body: 7u32,
    };
    total(small, large)
}

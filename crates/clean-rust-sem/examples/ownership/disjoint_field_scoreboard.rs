// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

struct Scoreboard {
    hits: u32,
    misses: u32,
}

fn main() -> u32 {
    let mut board = Scoreboard {
        hits: 4u32,
        misses: 1u32,
    };
    let hits_view: &u32 = &board.hits;
    board.misses = board.misses + 1u32;
    *hits_view + board.misses
}

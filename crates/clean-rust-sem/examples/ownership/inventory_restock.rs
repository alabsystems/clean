// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

struct Inventory {
    on_hand: u32,
    last_received: u32,
}

impl Inventory {
    fn snapshot(&self) -> u32 {
        self.on_hand
    }

    fn restock(&mut self, delivery: u32) -> u32 {
        self.last_received = delivery;
        self.on_hand = self.on_hand + delivery;
        self.on_hand
    }
}

fn main() -> u32 {
    let mut inventory = Inventory {
        on_hand: 3u32,
        last_received: 0u32,
    };
    let updated = inventory.restock(inventory.snapshot());
    updated + inventory.last_received
}

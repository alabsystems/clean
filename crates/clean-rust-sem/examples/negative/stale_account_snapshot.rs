// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

struct Account {
    cents: u32,
}

fn main() -> u32 {
    let mut account = Account { cents: 10u32 };
    let snapshot: &u32 = &account.cents;
    account.cents = account.cents + 5u32;
    *snapshot
}

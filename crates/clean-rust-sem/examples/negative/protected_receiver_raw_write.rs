// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

struct Session {
    requests: u32,
}

impl Session {
    fn read_after_admin_write(&self, raw: *mut Session) -> u32 {
        unsafe {
            *raw = Session { requests: 7u32 };
        }
        self.requests
    }
}

fn main() -> u32 {
    let mut session = Session { requests: 1u32 };
    let raw: *mut Session = (&mut session) as *mut Session;
    let shared: &Session = &session;
    shared.read_after_admin_write(raw)
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::interpret::InterpretOptions;

struct Bytes(usize);
impl ExecutionObserver for Bytes {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.0 = self
            .0
            .checked_sub(event.copy_bytes)
            .ok_or("requested bytes")?;
        Ok(())
    }
}

#[test]
fn first_borrowed_frontier_growth_is_refused_before_allocation() {
    let root = Ty::Bool;
    let mut tasks = Vec::new();
    let mut observer = Bytes(size_of::<Work<'_, '_, Bytes>>());
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let site = ExecutionSite::Entry(crate::FuncId::new(79));
    let mut work = Work::new(&mut session, site).unwrap();
    assert!(matches!(
        work.push(&mut tasks, Task::Type(&root)),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    assert_eq!((tasks.len(), tasks.capacity()), (0, 0));
    work.retire_copy_vec(tasks);
    work.retire_scratch();
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "requested bytes"
    );
    assert_eq!(
        work.session.remaining_fuel(),
        InterpretOptions::default().fuel
    );
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl NativeBuild {
    pub(super) fn constant<O: ExecutionObserver>(
        &mut self,
        value: &Constant,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed<()> {
        let mut pending = Vec::new();
        let result = (|| {
            let mut current = Some(value);
            loop {
                admit(session, site, 1, 0)?;
                if let Some(value) = current.take() {
                    match constant_reach(value) {
                        ConstantReach::Nothing => {}
                        // No callable creation or symbol resolution is hidden
                        // inside a successful empty-universe native graph.
                        _ => return Err(ObservedValueError::UnsupportedValue),
                    }
                    let mut children = value.children();
                    current = children.next();
                    if children.len() > 0 {
                        push(&mut pending, children, session, site)?;
                    }
                } else if let Some(children) = pending.last_mut() {
                    current = children.next();
                    if children.len() == 0 {
                        pending.pop();
                    }
                } else {
                    break;
                }
            }
            Ok(())
        })();
        retire_vec(pending, session, site);
        result
    }
}

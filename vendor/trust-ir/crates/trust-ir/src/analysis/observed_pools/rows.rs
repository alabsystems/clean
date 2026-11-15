// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use core::cmp::Ordering;

impl<'a> Closing<'a> {
    pub(super) fn members<O: ExecutionObserver>(
        &mut self,
        universe: &'a IndirectCallUniverse,
        launders_any_dyn: bool,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed {
        for fact in &universe.members {
            admit(session, site, 1, 0)?;
            let key = Key::of(&fact.key);
            self.file(
                fact.member,
                key,
                fact.confined,
                launders_any_dyn,
                session,
                site,
            )?;
            if let Some(principal) = key.principal() {
                lookup(self.output.upcast_reach.len(), session, site)?;
                // Borrow the map separately: filing touches only rows/demotion.
                if let Some(reached) = self.output.upcast_reach.get(&principal) {
                    for target in reached {
                        admit(session, site, 1, 0)?;
                        file(
                            &mut self.rows,
                            &self.demoted,
                            Row {
                                member: fact.member,
                                key: key.with_principal(*target),
                                confined: fact.confined,
                            },
                            launders_any_dyn,
                            session,
                            site,
                        )?;
                    }
                }
            }
        }
        sort(&mut self.rows, &mut self.row_scratch, session, site)?;
        self.emit_members(session, site)
    }

    fn emit_members<O: ExecutionObserver>(
        &mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed {
        let mut position = 0;
        while position < self.rows.len() {
            admit(session, site, 1, 0)?;
            let mut row = self.rows[position];
            position += 1;
            while position < self.rows.len() {
                if compare(row, self.rows[position], session, site)? != Ordering::Equal {
                    break;
                }
                admit(session, site, 1, size_of::<bool>())?;
                row.confined &= self.rows[position].confined;
                position += 1;
            }
            reserve(&mut self.output.members, session, site)?;
            self.pending_key = Some(keys::copy_key(row.key, session, site)?);
            admit(session, site, 1, size_of::<PoolMember>())?;
            let Some(key) = self.pending_key.take() else {
                return Err(ObservedValueError::InvalidRange);
            };
            self.output.members.push(PoolMember {
                member: row.member,
                key,
                confined: row.confined,
            });
        }
        Ok(())
    }

    fn file<O: ExecutionObserver>(
        &mut self,
        member: ReachNode,
        key: Key<'a>,
        confined: bool,
        launders_any_dyn: bool,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed {
        file(
            &mut self.rows,
            &self.demoted,
            Row {
                member,
                key,
                confined,
            },
            launders_any_dyn,
            session,
            site,
        )
    }

    pub(super) fn copy_launders<O: ExecutionObserver>(
        &mut self,
        universe: &IndirectCallUniverse,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Observed {
        for (key, source) in &universe.laundered {
            admit(session, site, 1, 0)?;
            if let CarriedKey::Key(PoolKey::Fn(shape)) = key
                && shape
                    .params
                    .as_ref()
                    .is_some_and(|params| !params.is_empty())
                && !insert(
                    &mut self.shape_prefixes,
                    (shape.abi, shape.variadic),
                    session,
                    site,
                )?
            {
                // Inserting this key could compare two nonempty parameter
                // vectors inside std Ord. A prior scan cannot observe it.
                return Err(ObservedValueError::UnsupportedValue);
            }
            self.pending_carried = Some(keys::copy_carried(key, session, site)?);
            tree_growth::<CarriedKey, ReachSite, O>(self.output.laundered.len(), session, site)?;
            admit(session, site, 1, size_of::<(CarriedKey, ReachSite)>())?;
            let Some(copied) = self.pending_carried.take() else {
                return Err(ObservedValueError::InvalidRange);
            };
            self.output.laundered_fn |= key.may_be_fn();
            self.output.laundered.insert(copied, *source);
        }
        Ok(())
    }
}

fn file<'a, O: ExecutionObserver>(
    rows: &mut Vec<Row<'a>>,
    demoted: &BTreeSet<PrincipalKey>,
    mut row: Row<'a>,
    launders_any_dyn: bool,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed {
    admit(session, site, 1, 0)?;
    row.confined = row.confined && !launders_any_dyn;
    if row.confined
        && let Some(principal) = row.key.principal()
    {
        row.confined = !contains(demoted, &principal, session, site)?;
    }
    push(rows, row, session, site)
}

fn compare<O: ExecutionObserver>(
    left: Row<'_>,
    right: Row<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed<Ordering> {
    admit(session, site, 1, 0)?;
    let member = left.member.cmp(&right.member);
    if member != Ordering::Equal {
        return Ok(member);
    }
    keys::compare(left.key, right.key, session, site)
}

/// Stable bottom-up merge sort, followed by the original per-key AND merge.
/// Borrowed rows permit actual parameter comparisons without std B-tree Ord;
/// sorting avoids quadratic insertion shifts on large universes.
fn sort<'a, O: ExecutionObserver>(
    rows: &mut Vec<Row<'a>>,
    scratch: &mut Vec<Row<'a>>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Observed {
    for row in rows.iter() {
        push(scratch, *row, session, site)?;
    }
    let mut width = 1usize;
    while width < rows.len() {
        admit(session, site, 1, 0)?;
        let mut start = 0usize;
        while start < rows.len() {
            admit(session, site, 1, 0)?;
            let middle = start.saturating_add(width).min(rows.len());
            let end = middle.saturating_add(width).min(rows.len());
            let (mut left, mut right) = (start, middle);
            for destination in &mut scratch[start..end] {
                admit(session, site, 1, size_of::<Row<'_>>())?;
                let from_left = right == end
                    || left < middle
                        && compare(rows[left], rows[right], session, site)? != Ordering::Greater;
                if from_left {
                    *destination = rows[left];
                    left += 1;
                } else {
                    *destination = rows[right];
                    right += 1;
                }
            }
            start = end;
        }
        core::mem::swap(rows, scratch);
        width = width.saturating_mul(2);
    }
    Ok(())
}

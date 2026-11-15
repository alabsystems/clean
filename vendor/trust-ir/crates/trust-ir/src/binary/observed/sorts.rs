// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

type Fields = [(String, ClauseSort)];
type Constructors = [(String, Vec<(String, ClauseSort)>)];
enum Task<'a> {
    Sort(&'a ClauseSort),
    Constructors(&'a Constructors),
    Fields(&'a Fields),
}

pub(super) fn observed_write_clause_sort<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    sort: &ClauseSort,
) -> R {
    let mut tasks = Vec::new();
    let result = (|| {
        buf.push_value(&mut tasks, Task::Sort(sort))?;
        while !tasks.is_empty() {
            buf.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                Task::Sort(sort) => write_head(buf, pool, sort, &mut tasks)?,
                Task::Constructors(rows) => {
                    if let Some(((name, fields), rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            buf.push_value(&mut tasks, Task::Constructors(rest))?;
                        }
                        observed_write_str(buf, pool, name)?;
                        observed_write_count(
                            buf,
                            "ClauseSort::Datatype constructor fields",
                            fields.len(),
                        )?;
                        buf.push_value(&mut tasks, Task::Fields(fields))?;
                    }
                }
                Task::Fields(rows) => {
                    if let Some(((name, sort), rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            buf.push_value(&mut tasks, Task::Fields(rest))?;
                        }
                        observed_write_str(buf, pool, name)?;
                        buf.push_value(&mut tasks, Task::Sort(sort))?;
                    }
                }
            }
        }
        Ok(())
    })();
    buf.finish_child(result, tasks)
}
fn write_head<'a, O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    sort: &'a ClauseSort,
    tasks: &mut Vec<Task<'a>>,
) -> R {
    match sort {
        ClauseSort::Bool => observed_write_u8(buf, 0)?,
        ClauseSort::Int => observed_write_u8(buf, 1)?,
        ClauseSort::BitVec(width) => {
            observed_write_u8(buf, 2)?;
            observed_write_v32(buf, *width)?;
        }
        ClauseSort::Array(key, value) => {
            observed_write_u8(buf, 3)?;
            buf.push_value(tasks, Task::Sort(value))?;
            buf.push_value(tasks, Task::Sort(key))?;
        }
        ClauseSort::Float { eb, sb } => {
            observed_write_u8(buf, 4)?;
            observed_write_v32(buf, *eb)?;
            observed_write_v32(buf, *sb)?;
        }
        ClauseSort::RoundingMode => observed_write_u8(buf, 5)?,
        ClauseSort::Datatype { name, constructors } => {
            observed_write_u8(buf, 6)?;
            observed_write_str(buf, pool, name)?;
            observed_write_count(buf, "ClauseSort::Datatype constructors", constructors.len())?;
            buf.push_value(tasks, Task::Constructors(constructors))?;
        }
    }
    Ok(())
}

pub(super) fn observed_collect_clause_sort_strings<O: ExecutionObserver>(
    sort: &ClauseSort,
    pool: &mut Builder,
    out: &mut Output<'_, '_, O>,
) -> R {
    let mut tasks = Vec::new();
    let result = (|| {
        out.push_value(&mut tasks, Task::Sort(sort))?;
        while !tasks.is_empty() {
            out.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                Task::Sort(ClauseSort::Array(key, value)) => {
                    out.push_value(&mut tasks, Task::Sort(value))?;
                    out.push_value(&mut tasks, Task::Sort(key))?;
                }
                Task::Sort(ClauseSort::Datatype { name, constructors }) => {
                    pool.intern(name, out)?;
                    out.push_value(&mut tasks, Task::Constructors(constructors))?;
                }
                Task::Sort(_) => {}
                Task::Constructors(rows) => {
                    if let Some(((name, fields), rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            out.push_value(&mut tasks, Task::Constructors(rest))?;
                        }
                        pool.intern(name, out)?;
                        out.push_value(&mut tasks, Task::Fields(fields))?;
                    }
                }
                Task::Fields(rows) => {
                    if let Some(((name, sort), rest)) = rows.split_first() {
                        if !rest.is_empty() {
                            out.push_value(&mut tasks, Task::Fields(rest))?;
                        }
                        pool.intern(name, out)?;
                        out.push_value(&mut tasks, Task::Sort(sort))?;
                    }
                }
            }
        }
        Ok(())
    })();
    out.finish_child(result, tasks)
}

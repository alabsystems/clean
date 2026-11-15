// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Kind {
    Struct,
    Enum,
    Record,
    Closure,
    Func,
    TyId,
    Pred,
}
pub(super) type Key = (Kind, u32, u32);
#[derive(Clone, Copy)]
pub(super) struct ConflictSource<'a> {
    pub origin: &'a TypeOrigin,
    pub table: &'static str,
    pub left: &'a str,
    pub right: &'a str,
}
#[derive(Clone, Copy)]
pub(super) enum Direction {
    Forward,
    Reverse,
}
pub(super) enum Task<'a> {
    Ty(&'a Ty, &'a Ty),
    Id(TyId, TyId),
    Nominal(Kind, u32, u32),
    Pred(PredId, PredId),
    Types(&'a [Ty], &'a [Ty]),
    Fields(&'a [FieldDef], &'a [FieldDef]),
    Variants(&'a [EnumVariant], &'a [EnumVariant]),
    EnumTail(&'a EnumDef, &'a EnumDef),
    End(Key, Option<ConflictSource<'a>>),
    SetRow(&'a [PredId], &'a [PredId], Direction, usize),
    SetAny(&'a [PredId], &'a [PredId], Direction, usize, usize),
    Constant(&'a Constant, &'a Constant),
    Constants(&'a [Constant], &'a [Constant]),
    ConstantFields(&'a [(String, Constant)], &'a [(String, Constant)]),
}
pub(super) struct State<'a> {
    pub tasks: Vec<Task<'a>>,
    pub active: Vec<Key>,
    pub last: bool,
    pub conflict: Option<TypeOriginConflict>,
    pub pending_origin: Option<TypeOrigin>,
    pub pending_left: String,
    pub pending_right: String,
    pub discs_a: Option<Vec<i128>>,
    pub discs_b: Option<Vec<i128>>,
}
impl<'a> State<'a> {
    pub fn new() -> Self {
        Self {
            tasks: Vec::new(),
            active: Vec::new(),
            last: true,
            conflict: None,
            pending_origin: None,
            pending_left: String::new(),
            pending_right: String::new(),
            discs_a: None,
            discs_b: None,
        }
    }
    pub fn push<O: ExecutionObserver>(&mut self, task: Task<'a>, w: &mut Work<'_, '_, O>) -> R {
        w.reserve(&mut self.tasks)?;
        w.admit(1, size_of::<Task<'a>>())?;
        self.tasks.push(task);
        Ok(())
    }
    pub fn enter<O: ExecutionObserver>(
        &mut self,
        key: Key,
        source: Option<ConflictSource<'a>>,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut rows = self.active.as_slice();
        loop {
            w.admit(1 + size_of::<Key>(), size_of::<Option<(&Key, &[Key])>>())?;
            let Some((row, rest)) = rows.split_first() else {
                break;
            };
            if *row == key {
                self.last = true;
                return Ok(false);
            }
            rows = rest;
        }
        w.reserve(&mut self.active)?;
        w.admit(1, size_of::<Key>())?;
        self.active.push(key);
        self.push(Task::End(key, source), w)?;
        Ok(true)
    }
    pub fn end<O: ExecutionObserver>(
        &mut self,
        key: Key,
        source: Option<ConflictSource<'a>>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1 + size_of::<Key>(), size_of::<Option<Key>>())?;
        if self.active.pop() != Some(key) {
            return Err(ObservedValueError::InvalidRange);
        }
        if !self.last
            && let Some(source) = source
        {
            self.note(source, w)?;
        }
        Ok(())
    }
    fn note<O: ExecutionObserver>(
        &mut self,
        source: ConflictSource<'a>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            1 + size_of::<TypeOriginConflict>() + size_of::<TypeOrigin>(),
            size_of::<TypeOriginConflict>(),
        )?;
        if self.conflict.is_some() {
            return Ok(());
        }
        self.pending_origin = Some(match source.origin {
            TypeOrigin::Rust {
                stable_crate_id,
                def_path_hash,
                args_digest,
            } => TypeOrigin::Rust {
                stable_crate_id: *stable_crate_id,
                def_path_hash: *def_path_hash,
                args_digest: *args_digest,
            },
            TypeOrigin::Clean { decl, env_digest } => TypeOrigin::Clean {
                decl: w.copy_text(decl)?,
                env_digest: *env_digest,
            },
        });
        self.pending_left = w.copy_text(source.left)?;
        self.pending_right = w.copy_text(source.right)?;
        let Some(origin) = self.pending_origin.take() else {
            return Err(ObservedValueError::InvalidRange);
        };
        self.conflict = Some(TypeOriginConflict {
            origin,
            table: source.table,
            left: core::mem::take(&mut self.pending_left),
            right: core::mem::take(&mut self.pending_right),
        });
        Ok(())
    }
    pub fn scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.retire_rows(&mut self.tasks);
        w.retire_rows(&mut self.active);
        self.discriminants(w);
        if let Some(origin) = self.pending_origin.take() {
            retire_origin(origin, w);
        }
        w.retire_text(core::mem::take(&mut self.pending_left));
        w.retire_text(core::mem::take(&mut self.pending_right));
    }
    pub fn discriminants<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        for slot in [&mut self.discs_a, &mut self.discs_b] {
            w.session
                .retirement_step(w.site, size_of::<Option<Vec<i128>>>() + 1);
            if let Some(mut rows) = slot.take() {
                w.retire_rows(&mut rows);
            }
        }
    }
    pub fn owned<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        if let Some(conflict) = self.conflict.take() {
            retire_conflict(conflict, w);
        }
    }
}
pub(super) fn retire_origin<O: ExecutionObserver>(origin: TypeOrigin, w: &mut Work<'_, '_, O>) {
    w.session
        .retirement_step(w.site, size_of::<TypeOrigin>() + 1);
    if let TypeOrigin::Clean { decl, .. } = origin {
        w.retire_text(decl);
    }
    w.session.retirement_poll(w.site);
}
pub(super) fn retire_conflict<O: ExecutionObserver>(
    conflict: TypeOriginConflict,
    w: &mut Work<'_, '_, O>,
) {
    w.session
        .retirement_step(w.site, size_of::<TypeOriginConflict>() + 1);
    retire_origin(conflict.origin, w);
    w.retire_text(conflict.left);
    w.retire_text(conflict.right);
    w.session.retirement_poll(w.site);
}

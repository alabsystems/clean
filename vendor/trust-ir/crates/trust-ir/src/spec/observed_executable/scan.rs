// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
pub(super) enum Role {
    Action,
    Projection,
}
impl Role {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Action => "action",
            Self::Projection => "projection",
        }
    }
    fn spelling(self) -> &'static str {
        match self {
            Self::Action => "rust_symbol",
            Self::Projection => "project",
        }
    }
}
impl<'a> State<'a> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(spec) = work.at(&module.spec_modules, index)? {
            let mut at = 0;
            while let Some(anchor) = work.at(&spec.anchors, at)? {
                if !work.blank(&spec.name)?
                    && !work.blank(&anchor.machine)?
                    && !work.blank(&anchor.action)?
                    && work.equal(&anchor.machine, &spec.name)?
                {
                    work.admit(1, size_of::<Option<FuncId>>() + size_of::<Role>())?;
                    if let Some(function) = anchor.function {
                        self.target(
                            module,
                            spec,
                            anchor,
                            Role::Action,
                            function,
                            &anchor.rust_symbol,
                            work,
                        )?;
                    }
                    work.admit(
                        3,
                        size_of::<Option<SpecProjectionTarget>>()
                            + size_of::<Role>()
                            + size_of::<&str>(),
                    )?;
                    match anchor.projection_target {
                        Some(SpecProjectionTarget::Function(function)) => self.target(
                            module,
                            spec,
                            anchor,
                            Role::Projection,
                            function,
                            anchor.project.as_deref().unwrap_or_default(),
                            work,
                        )?,
                        Some(SpecProjectionTarget::TemporalFieldPathsV1)
                        | Some(SpecProjectionTarget::ExternalUnresolved)
                        | None => {}
                    }
                }
                work.next(&mut at)?;
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    #[allow(
        clippy::too_many_arguments,
        reason = "the observed twin keeps the unobserved signature and adds the session"
    )]
    fn target<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        spec: &SpecModule,
        anchor: &SpecAnchor,
        role: Role,
        function: FuncId,
        expected: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        let mut count = 0usize;
        let mut at = 0;
        while let Some(candidate) = work.at(&module.functions, at)? {
            work.admit(1, 2 * size_of::<u32>())?;
            if candidate.id.index() == function.index() {
                work.next(&mut count)?;
            }
            work.next(&mut at)?;
        }
        work.admit(1, 0)?;
        if count > 1 {
            self.begin(work)?;
            work.text("function id is ambiguous (", &mut self.detail)?;
            work.number(count as u128, &mut self.detail)?;
            work.text(" definitions)", &mut self.detail)?;
            return self.issue(spec, anchor, role, function, work);
        }
        let Some(linked) = lookup(module, function, work)? else {
            self.begin(work)?;
            work.text("function id is not present in module ", &mut self.detail)?;
            work.quoted(&module.name, &mut self.detail)?;
            return self.issue(spec, anchor, role, function, work);
        };
        work.admit(1, 0)?;
        if linked.blocks.is_empty() {
            self.begin(work)?;
            work.text("function is a bodyless declaration", &mut self.detail)?;
            return self.issue(spec, anchor, role, function, work);
        }
        if !work.blank(expected)? && !work.equal(&linked.name, expected)? {
            self.begin(work)?;
            work.admit(2, size_of::<Role>())?;
            work.text(role.spelling(), &mut self.detail)?;
            work.text(" ", &mut self.detail)?;
            work.quoted(expected, &mut self.detail)?;
            work.text(" does not match typed target ", &mut self.detail)?;
            work.quoted(&linked.name, &mut self.detail)?;
            return self.issue(spec, anchor, role, function, work);
        }
        work.admit(2, 0)?;
        if matches!(role, Role::Action) {
            return Ok(());
        }
        let Some(signature) = work.at(&module.func_types, linked.ty.index() as usize)? else {
            self.begin(work)?;
            work.text(
                "function references missing signature type #",
                &mut self.detail,
            )?;
            work.number(linked.ty.index() as u128, &mut self.detail)?;
            return self.issue(spec, anchor, role, function, work);
        };
        work.admit(4, size_of::<bool>())?;
        let conforms = if !signature.is_vararg
            && signature.params.len() == 1
            && signature.returns.len() == 1
        {
            let parameter = work
                .at(&signature.params, 0)?
                .ok_or(ObservedValueError::InvalidRange)?;
            matches!(parameter, Ty::Ref(_))
        } else {
            false
        };
        if !conforms {
            self.begin(work)?;
            work.text(
                "projection signature must be non-variadic (&T) -> R, got params=",
                &mut self.detail,
            )?;
            self.types_text(&signature.params, work)?;
            work.text(", returns=", &mut self.detail)?;
            self.types_text(&signature.returns, work)?;
            work.text(", vararg=", &mut self.detail)?;
            work.admit(1, size_of::<bool>())?;
            work.text(
                if signature.is_vararg { "true" } else { "false" },
                &mut self.detail,
            )?;
            self.issue(spec, anchor, role, function, work)?;
        }
        Ok(())
    }
}
/// Exact direct-slot-first, then first-physical fallback, after the original
/// complete duplicate count has already refused ambiguous IDs.
fn lookup<'a, O: ExecutionObserver>(
    module: &'a Module,
    id: FuncId,
    work: &mut Work<'_, '_, O>,
) -> R<Option<&'a Function>> {
    if let Some(row) = work.at(&module.functions, id.index() as usize)? {
        work.admit(1, 2 * size_of::<u32>())?;
        if row.id.index() == id.index() {
            return Ok(Some(row));
        }
    }
    let mut at = 0;
    while let Some(row) = work.at(&module.functions, at)? {
        work.admit(1, 2 * size_of::<u32>())?;
        if row.id.index() == id.index() {
            return Ok(Some(row));
        }
        work.next(&mut at)?;
    }
    Ok(None)
}

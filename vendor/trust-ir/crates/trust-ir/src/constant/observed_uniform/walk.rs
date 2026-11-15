// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'a> State<'a> {
    fn children<O: ExecutionObserver>(
        node: &'a Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R<ConstantChildren<'a>> {
        work.admit(64, size_of::<ConstantChildren<'_>>())?;
        Ok(node.children())
    }
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        root: &'a Constant,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let children = Self::children(root, work)?;
        work.admit(1, size_of::<bool>())?;
        if children.len() == 0 {
            return Ok(());
        }
        work.reserve(&mut self.stack)?;
        work.admit(1, size_of::<Frame<'_>>())?;
        self.stack.push(Frame {
            node: root,
            children,
            first: 0,
        });
        loop {
            work.admit(1, size_of::<Option<&mut Frame<'_>>>())?;
            let Some(frame) = self.stack.last_mut() else {
                return Ok(());
            };
            work.admit(4, size_of::<Option<&Constant>>())?;
            if let Some(child) = frame.children.next() {
                let children = Self::children(child, work)?;
                work.reserve(&mut self.stack)?;
                work.admit(2, size_of::<Frame<'_>>())?;
                self.stack.push(Frame {
                    node: child,
                    children,
                    first: self.results.len(),
                });
                continue;
            }
            work.admit(1, size_of::<Option<Frame<'_>>>())?;
            self.current = self.stack.pop();
            let frame = self
                .current
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?;
            let node = frame.node;
            let first = frame.first;
            work.admit(32, size_of::<Option<Key<'_>>>())?;
            if self.building.is_some() || self.pending_key.is_some() {
                return Err(ObservedValueError::InvalidRange);
            }
            match node {
                Constant::Int(value) => self.building = Some(Key::Int(*value)),
                Constant::Bytes { data, utf8: false } => {
                    self.building = Some(Key::Composite {
                        variant: None,
                        payload: 0,
                        labels: &[],
                        children: Vec::new(),
                    });
                    let mut at = 0;
                    while let Some(byte) = work.at(data, at)? {
                        work.admit(1, size_of::<Option<Key<'_>>>())?;
                        self.pending_key = Some(Key::Int(i128::from(*byte)));
                        let class = self.intern(None, work)?;
                        self.push_child(class, work)?;
                        work.next(&mut at)?;
                    }
                }
                Constant::U128(_)
                | Constant::Bytes { .. }
                | Constant::Float(_)
                | Constant::Bool(_)
                | Constant::FnDef(_)
                | Constant::SymbolAddr { .. }
                | Constant::PhantomData
                // v70: a leaf keyed by its digest and extents (no constant children).
                | Constant::TensorBlob { .. } => self.building = Some(Key::Leaf(node)),
                _ => {
                    let list = matches!(node, Constant::Array(_) | Constant::Aggregate(_));
                    self.building = Some(Key::Composite {
                        variant: if list {
                            None
                        } else {
                            Some(core::mem::discriminant(node))
                        },
                        payload: match node {
                            Constant::Closure { func, .. } => u64::from(func.index()),
                            Constant::Splat { len, .. } => *len,
                            _ => 0,
                        },
                        labels: match node {
                            Constant::Record(fields) => fields,
                            _ => &[],
                        },
                        children: Vec::new(),
                    });
                    work.admit(1, size_of::<bool>())?;
                    if first > self.results.len() {
                        return Err(ObservedValueError::InvalidRange);
                    }
                    while self.results.len() > first {
                        let Some(Key::Composite { children, .. }) = self.building.as_mut() else {
                            return Err(ObservedValueError::InvalidRange);
                        };
                        work.reserve(children)?;
                        work.admit(2, size_of::<usize>())?;
                        let value = self.results.pop().ok_or(ObservedValueError::InvalidRange)?;
                        children.push(value);
                    }
                    let Some(Key::Composite { children, .. }) = self.building.as_mut() else {
                        return Err(ObservedValueError::InvalidRange);
                    };
                    work.admit(2, 2 * size_of::<usize>())?;
                    let mut at = 0;
                    let mut end = children.len();
                    while at < end {
                        work.admit(4, 2 * size_of::<usize>())?;
                        end -= 1;
                        if at >= end {
                            break;
                        }
                        children.swap(at, end);
                        work.next(&mut at)?;
                    }
                    if list && self.is_uniform(work)? {
                        work.reserve(&mut self.uniform)?;
                        work.admit(1, size_of::<usize>())?;
                        self.uniform.push(node as *const Constant as usize);
                    }
                }
            }
            work.admit(1, size_of::<Option<Key<'_>>>())?;
            self.pending_key = self.building.take();
            let class = self.intern(Some(node), work)?;
            work.reserve(&mut self.results)?;
            work.admit(1, size_of::<usize>())?;
            self.results.push(class);
            work.retire(self.current.take());
            work.admit(1, 0)?;
        }
    }
    fn push_child<O: ExecutionObserver>(&mut self, class: usize, work: &mut Work<'_, '_, O>) -> R {
        let Some(Key::Composite { children, .. }) = self.building.as_mut() else {
            return Err(ObservedValueError::InvalidRange);
        };
        work.reserve(children)?;
        work.admit(1, size_of::<usize>())?;
        children.push(class);
        Ok(())
    }
    fn is_uniform<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R<bool> {
        let Some(Key::Composite { children, .. }) = self.building.as_ref() else {
            return Err(ObservedValueError::InvalidRange);
        };
        work.admit(1, size_of::<bool>())?;
        if children.len() < 2 {
            return Ok(false);
        }
        let first = work
            .at(children, 0)?
            .ok_or(ObservedValueError::InvalidRange)?;
        let mut at = 0;
        while let Some(child) = work.at(children, at)? {
            work.admit(1, size_of::<bool>())?;
            if child != first {
                return Ok(false);
            }
            work.next(&mut at)?;
        }
        Ok(true)
    }
}

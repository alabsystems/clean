// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test-only observations of ordinary checked source registration.
use super::{SpecError, Specification};
use clean_elab::{ElabError, ElabResult};
use clean_kernel::{ConstantInfo, Environment, Name};
use std::{cell::RefCell, time::Instant};

#[derive(Clone, Debug)]
pub(super) struct Event {
    data: EventData,
    started: Instant,
}

// Read-only outside this module. There is deliberately no Event constructor,
// Deserialize implementation, DerefMut, or metadata-to-observation conversion.
impl std::ops::Deref for Event {
    type Target = EventData;
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

#[derive(Clone, Debug)]
pub(super) struct EventData {
    pub source: String,
    pub kind: &'static str,
    pub header: String,
    pub absent_before: bool,
    pub returned_name: Option<String>,
    pub elaborator_error: Option<ElabError>,
    pub outcome: Option<String>,
    pub accepted: bool,
    pub kernel: Option<ConstantInfo>,
    pub family: serde_json::Value,
    pub verification: Option<clean_kernel::DeclarationVerification>,
    pub ticks: u64,
    pub limit: u64,
    pub exhausted: bool,
    pub seconds: f64,
}

thread_local! {
    static LOG: RefCell<Option<Vec<Event>>> = const { RefCell::new(None) };
}

pub(super) struct Capture {
    _same_thread: std::marker::PhantomData<std::rc::Rc<()>>,
}
impl Capture {
    pub(super) fn start() -> Self {
        LOG.with(|log| {
            let mut log = log.borrow_mut();
            assert!(log.is_none(), "nested source observer");
            *log = Some(Vec::new());
        });
        Self {
            _same_thread: std::marker::PhantomData,
        }
    }
    pub(super) fn events(&self) -> Vec<Event> {
        LOG.with(|log| log.borrow().as_ref().expect("active observer").clone())
    }
    pub(super) fn last_event(&self) -> Option<Event> {
        LOG.with(|log| {
            log.borrow()
                .as_ref()
                .expect("active observer")
                .last()
                .cloned()
        })
    }
}
impl Drop for Capture {
    fn drop(&mut self) {
        LOG.with(|log| *log.borrow_mut() = None);
    }
}

pub(super) fn begin(env: &Environment, kind: &'static str, source: &str) -> Option<usize> {
    LOG.with(|log| {
        let mut log = log.borrow_mut();
        let events = log.as_mut()?;
        // Only a pre-call name-absence observation. The owner authenticates the
        // complete declaration AST and joins returned_name after elaboration.
        let header = source.split_whitespace().nth(1).unwrap_or("").to_owned();
        let index = events.len();
        events.push(Event {
            data: EventData {
                absent_before: env.get_const(&Name::from_string(&header)).is_none(),
                source: source.to_owned(),
                kind,
                header,
                returned_name: None,
                elaborator_error: None,
                outcome: None,
                accepted: false,
                kernel: None,
                family: serde_json::Value::Null,
                verification: None,
                ticks: 0,
                limit: 0,
                exhausted: false,
                seconds: 0.0,
            },
            started: Instant::now(),
        });
        Some(index)
    })
}

pub(super) fn elaborator_error(error: &ElabError) {
    LOG.with(|log| {
        if let Some(event) = log
            .borrow_mut()
            .as_mut()
            .and_then(|v| v.last_mut())
            .map(|e| &mut e.data)
        {
            event.elaborator_error = Some(error.clone());
        }
    });
}

pub(super) fn elaborator_result(result: &ElabResult) {
    let name = match result {
        ElabResult::Definition { name, .. }
        | ElabResult::Theorem { name, .. }
        | ElabResult::Inductive { name, .. } => Some(name.to_string()),
        _ => None, // The ordinary methods refuse every other result shape.
    };
    LOG.with(|log| {
        if let Some(event) = log
            .borrow_mut()
            .as_mut()
            .and_then(|v| v.last_mut())
            .map(|e| &mut e.data)
        {
            event.returned_name = name;
        }
    });
}

pub(super) fn family(env: &Environment, root: &Name) -> serde_json::Value {
    let Some(inductive) = env.get_inductive(root) else {
        return serde_json::Value::Null;
    };
    let constructors: Vec<_> = inductive
        .constructor_names
        .iter()
        .map(|name| env.get_constructor(name).expect("registered constructor"))
        .collect();
    let mut recursors: Vec<_> = env
        .recursors()
        .filter(|r| &r.inductive_name == root)
        .collect();
    recursors.sort_by_key(|r| r.name.to_string());
    let names: Vec<_> = std::iter::once(root)
        .chain(inductive.constructor_names.iter())
        .chain(recursors.iter().map(|r| &r.name))
        .collect();
    let constants: Vec<_> = names
        .iter()
        .map(|name| {
            (
                env.get_const(name).expect("actual family constant"),
                env.declaration_verification(name),
            )
        })
        .collect();
    serde_json::json!({"inductive": inductive, "constructors": constructors, "recursors": recursors,"constants_and_provenance":constants})
}

pub(super) fn finish(index: Option<usize>, spec: &Specification, outcome: &Result<(), SpecError>) {
    let Some(index) = index else { return };
    LOG.with(|log| {
        let mut log = log.borrow_mut();
        let event = &mut log.as_mut().expect("active observer")[index];
        let seconds = event.started.elapsed().as_secs_f64();
        let event = &mut event.data;
        event.seconds = seconds;
        event.accepted = outcome.is_ok();
        event.outcome = Some(format!("{outcome:?}"));
        event.ticks = clean_kernel::tc::declaration_budget_used();
        event.limit = clean_kernel::tc::declaration_budget_limit();
        event.exhausted = clean_kernel::tc::declaration_budget_exhausted();
        let root = Name::from_string(&event.header);
        event.kernel = spec.env().get_const(&root).cloned();
        event.family = family(spec.env(), &root);
        event.verification = spec.env().declaration_verification(&root);
    });
}
